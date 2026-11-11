-- Prove2me | solution 1 for QuantumMaxCutEnergy.PauliSDP.strict_gap_0614
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:33:01.631198+00:00
-- url     : https://prove2.me/submissions/5ab77fe5-e024-45a5-966f-9d3f1b4fb768

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_physical_state_upper_bound
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_value_wellposed_bounds
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_moment_positive_excess_star
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_moment_correlation_range
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_exists_unit_correlation
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_restriction_feasible
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_full_level_exact
import Theorems.Thm_QuantumMaxCutEnergy_unweighted_optimum_le
import Theorems.Thm_QuantumMaxCutEnergy_positive_excess
import Theorems.Thm_QuantumMaxCutEnergy_small_odd_sets
import Theorems.Thm_QuantumMaxCutEnergy_matching_polytope_integral_rounding
import Theorems.Thm_QuantumMaxCutEnergy_PMatch_strict_scalar_0614
import Theorems.Thm_QuantumMaxCutEnergy_rank3_gaussian_rounding_quintic
import Theorems.Thm_QuantumMaxCutEnergy_pmatch_state_energy_lower
import Theorems.Thm_QuantumMaxCutEnergy_matching_polytope_real_rounding
import Theorems.Thm_QuantumMaxCutEnergy_matching_state_energy_lower
import Mathlib
open scoped BigOperators


noncomputable section

namespace QMCGap0614
open QuantumMaxCutEnergy QuantumMaxCutEnergy.PauliSDP

variable {n : ℕ}

/-- The SDP pair value on two vertices. -/
def G (L : Word n → ℝ) (i j : Fin n) : ℝ :=
  (1 - L (fun t => if t = i ∨ t = j then 1 else 0) -
    L (fun t => if t = i ∨ t = j then 2 else 0) -
    L (fun t => if t = i ∨ t = j then 3 else 0)) / 2

theorem G_comm (L : Word n → ℝ) (i j : Fin n) : G L i j = G L j i := by
  have h : ∀ a : Label, (fun t : Fin n => if t = i ∨ t = j then a else 0) =
      (fun t : Fin n => if t = j ∨ t = i then a else 0) := by
    intro a; funext t; exact if_congr or_comm rfl rfl
  unfold G
  rw [h 1, h 2, h 3]

/-- The positive excess of a pair value over one. -/
def F (L : Word n → ℝ) (i j : Fin n) : ℝ := max (G L i j - 1) 0

theorem F_comm (L : Word n → ℝ) (i j : Fin n) : F L i j = F L j i := by
  unfold F; rw [G_comm]

theorem F_nonneg (L : Word n → ℝ) (i j : Fin n) : 0 ≤ F L i j := le_max_right _ _

theorem star_sum (F : Fin n → Fin n → ℝ) (hF : ∀ i j, F i j = F j i) (v : Fin n) :
    (∑ e : Edge n, if v = e.val.1 ∨ v = e.val.2 then F e.val.1 e.val.2 else 0) =
      ∑ j ∈ Finset.univ.erase v, F v j := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
    (fun e _ => if v = e.val.1 then e.val.2 else e.val.1)
    (fun j hj => if h : v < j then (⟨(v, j), h⟩ : Edge n)
      else ⟨(j, v), lt_of_le_of_ne (not_lt.mp h) (Finset.ne_of_mem_erase hj)⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, hab⟩ he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    split_ifs with h
    · subst h; exact hab.ne'
    · rcases he with rfl | rfl
      · exact absurd rfl h
      · exact hab.ne
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · left; rfl
    · right; rfl
  · rintro ⟨⟨a, b⟩, hab⟩ he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    by_cases h : v = a
    · subst h
      simp [hab]
    · rcases he with rfl | rfl
      · exact absurd rfl h
      · simp [h, not_lt.mpr hab.le]
  · intro j hj
    by_cases h : v < j
    · simp [h]
    · have hjv : j < v := lt_of_le_of_ne (not_lt.mp h) (Finset.ne_of_mem_erase hj)
      simp [h, hjv.ne']
  · rintro ⟨⟨a, b⟩, hab⟩ he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    by_cases h : v = a
    · subst h
      simp
    · rcases he with rfl | rfl
      · exact absurd rfl h
      · simp [h, hF a v]

theorem odd_half (m : ℕ) (h : Odd m) : ((m / 2 : ℕ) : ℝ) = ((m : ℝ) - 1) / 2 := by
  obtain ⟨k, hk⟩ := h
  have h2 : m / 2 = k := by omega
  rw [h2, hk]
  push_cast
  ring

/-- Transport of an edge along an order embedding of the vertex set. -/
def edgeMap {s : ℕ} (ι : Fin s ↪o Fin n) (e : Edge s) : Edge n :=
  ⟨(ι e.val.1, ι e.val.2), ι.lt_iff_lt.2 e.property⟩

theorem edgeMap_injective {s : ℕ} (ι : Fin s ↪o Fin n) : Function.Injective (edgeMap ι) := by
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
  simp only [edgeMap, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 := ι.injective h1
  have e2 := ι.injective h2
  subst e1 e2
  rfl

theorem extend_twoBody {s : ℕ} (ι : Fin s ↪o Fin n) (a : Label) (e : Edge s) :
    Function.extend ι (twoBody a e) (fun _ => 0) = twoBody a (edgeMap ι e) := by
  funext t
  by_cases ht : ∃ i, ι i = t
  · obtain ⟨i, rfl⟩ := ht
    rw [ι.injective.extend_apply]
    simp only [twoBody, edgeMap, ι.injective.eq_iff]
  · rw [Function.extend_apply' _ _ _ ht]
    have hne : ¬ (t = ι e.val.1 ∨ t = ι e.val.2) := by
      rintro (rfl | rfl)
      · exact ht ⟨_, rfl⟩
      · exact ht ⟨_, rfl⟩
    exact (if_neg hne).symm

/-- Edge sets supported on at most `k` vertices: restrict, use exactness of the full level,
and the unweighted bound on the optimum. -/
theorem restricted_bound {s k : ℕ} (L : Word n → ℝ) (hL : Feasible k L) (ι : Fin s ↪o Fin n)
    (hs : s ≤ k) (E : Finset (Edge n))
    (hE : ∀ e ∈ E, e.val.1 ∈ Set.range ι ∧ e.val.2 ∈ Set.range ι) :
    (∑ e ∈ E, G L e.val.1 e.val.2) ≤ (E.card : ℝ) + ((s / 2 : ℕ) : ℝ) := by
  classical
  have hL' := restriction_feasible L hL ι ι.injective hs
  let w' : Weights s := fun e' => if edgeMap ι e' ∈ E then 1 else 0
  have hw' : ∀ e' : Edge s, w' e' = 0 ∨ w' e' = 1 := by
    intro e'
    by_cases h : edgeMap ι e' ∈ E
    · right; exact if_pos h
    · left; exact if_neg h
  have h1 := full_level_exact w' _ hL'
  have h2 := unweighted_optimum_le w' hw'
  have himg : (Finset.univ.filter (fun e' : Edge s => edgeMap ι e' ∈ E)).image (edgeMap ι) =
      E := by
    ext e
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e', he', rfl⟩
      exact he'
    · intro he
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hE e he
      have hij : i < j := by
        rw [← ι.lt_iff_lt, hi, hj]
        exact e.property
      have hee : edgeMap ι ⟨(i, j), hij⟩ = e := Subtype.ext (Prod.ext hi hj)
      exact ⟨⟨(i, j), hij⟩, by rw [hee]; exact he, hee⟩
  have hwcast : ∀ e' : Edge s, (w' e' : ℝ) = if edgeMap ι e' ∈ E then (1 : ℝ) else 0 := by
    intro e'
    by_cases h : edgeMap ι e' ∈ E
    · simp [w', h]
    · simp [w', h]
  have hc : (Finset.univ.filter (fun e' : Edge s => edgeMap ι e' ∈ E)).card = E.card := by
    rw [← Finset.card_image_of_injective _ (edgeMap_injective ι), himg]
  have hcard : (∑ e' : Edge s, (w' e' : ℝ)) = (E.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun e' _ => hwcast e'), Finset.sum_boole, hc]
  have hobj : objective w' (fun P : Word s => L (Function.extend ι P (fun _ => 0))) =
      ∑ e ∈ E, G L e.val.1 e.val.2 := by
    have hsum : (∑ e ∈ E, G L e.val.1 e.val.2) =
        ∑ e' ∈ Finset.univ.filter (fun e' : Edge s => edgeMap ι e' ∈ E),
          G L (edgeMap ι e').val.1 (edgeMap ι e').val.2 := by
      conv_lhs => rw [← himg]
      exact Finset.sum_image (fun a _ b _ h => edgeMap_injective ι h)
    rw [hsum, Finset.sum_filter]
    unfold objective
    refine Finset.sum_congr rfl (fun e' _ => ?_)
    rw [hwcast e']
    simp only [extend_twoBody]
    by_cases h : edgeMap ι e' ∈ E
    · rw [if_pos h, if_pos h, one_mul]
      rfl
    · rw [if_neg h, if_neg h]
      ring
  rw [hobj] at h1
  rw [hcard] at h2
  linarith

theorem pointwise (n : ℕ) (w : Weights n) (L : Word n → ℝ) (hL : Feasible 1999 L) :
    (0.6141 : ℝ) * objective w L ≤ optimum ⟨n, w⟩ := by
  classical
  have hk : (2 : ℕ) ≤ 1999 := by norm_num
  have hw : ∀ e : Edge n, (0 : ℝ) ≤ (w e : ℝ) := fun e => NNRat.cast_nonneg _
  -- the fractional matching
  have hx0 : ∀ e : Edge n, 0 ≤ F L e.val.1 e.val.2 := fun e => F_nonneg L _ _
  have hload : ∀ v : Fin n,
      (∑ e : Edge n, if v = e.val.1 ∨ v = e.val.2 then F L e.val.1 e.val.2 else 0) ≤ 1 := by
    intro v
    rw [star_sum (F L) (F_comm L) v]
    exact moment_positive_excess_star hk L hL v (Finset.univ.erase v) (by simp)
  have hsmall : ∀ S : Finset (Fin n), Odd S.card → S.card ≤ 2000 →
      (∑ e ∈ (Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S)),
        F L e.val.1 e.val.2) ≤ ((S.card : ℝ) - 1) / 2 := by
    intro S hodd h2000
    have h1999 : S.card ≤ 1999 := by
      obtain ⟨k, hk⟩ := hodd; omega
    refine positive_excess (fun e : Edge n => G L e.val.1 e.val.2) S ?_
    intro E hE
    have hb := restricted_bound L hL (S.orderEmbOfFin rfl) h1999 E (by
      intro e he
      have hm := Finset.mem_filter.1 (hE he)
      rw [Finset.range_orderEmbOfFin]
      exact ⟨hm.2.1, hm.2.2⟩)
    rw [odd_half _ hodd] at hb
    exact hb
  have hd : ((2000 : ℕ) : ℝ) / (((2000 : ℕ) : ℝ) + 1) = 2000 / 2001 := by norm_num
  obtain ⟨y, hydef⟩ : ∃ y : Edge n → ℝ, ∀ e, y e = ((2000 : ℝ) / 2001) * F L e.val.1 e.val.2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨hy0, hyload, hyodd⟩ :
      (∀ e : Edge n, 0 ≤ y e) ∧
      (∀ v : Fin n, (∑ e : Edge n, if v = e.val.1 ∨ v = e.val.2 then y e else 0) ≤ 1) ∧
      (∀ S : Finset (Fin n), Odd S.card →
        (∑ e ∈ (Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S)), y e) ≤
          ((S.card : ℝ) - 1) / 2) := by
    have h := small_odd_sets 2000 (fun e : Edge n => F L e.val.1 e.val.2) hx0 hload hsmall
    simp only [hd] at h
    simp only [hydef]
    exact h
  -- MATCH side
  obtain ⟨M, hM, hMw⟩ := matching_polytope_integral_rounding w y hy0 hyload hyodd
  have hA := matching_state_energy_lower w M hM
  have hQ : (∑ e : Edge n, (w e : ℝ) * (1 / 2 + (3 / 2) * y e)) ≤ optimum ⟨n, w⟩ := by
    have h : (∑ e : Edge n, (w e : ℝ) * (1 / 2 + (3 / 2) * y e)) =
        ((∑ e : Edge n, (w e : ℝ)) + 3 * ∑ e : Edge n, (w e : ℝ) * y e) / 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    rw [h]
    linarith
  -- PMATCH side
  obtain ⟨u, hu, hcorr⟩ := exists_unit_correlation hk L hL
  obtain ⟨a, hadef⟩ : ∃ a : Edge n → ℝ, ∀ e, a e = (w e : ℝ) *
      ((37241 / 38809 : ℝ) ^ 2 / 2 + (10920 / 38809 : ℝ) * (1 + 10920 / 38809) / 2 * y e) :=
    ⟨_, fun _ => rfl⟩
  have ha : ∀ e, 0 ≤ a e := fun e => by
    rw [hadef]
    exact mul_nonneg (hw e) (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (hy0 e)))
  obtain ⟨r, hr, hround⟩ := rank3_gaussian_rounding_quintic n a ha (Matrix.gram ℝ u)
    (Matrix.posSemidef_gram ℝ u)
    (fun i => by rw [Matrix.gram_apply, real_inner_self_eq_norm_sq, hu i]; norm_num)
  obtain ⟨t, htdef⟩ : ∃ t : Edge n → ℝ, ∀ e,
      t e = ∑ b : Fin 3, r e.val.1 b * r e.val.2 b := ⟨_, fun _ => rfl⟩
  obtain ⟨φ, hφdef⟩ : ∃ φ : Edge n → ℝ, ∀ e, φ e =
      (if Matrix.gram ℝ u e.val.1 e.val.2 ≤ 0 then
        0.84882 * Matrix.gram ℝ u e.val.1 e.val.2 +
          0.084882 * (Matrix.gram ℝ u e.val.1 e.val.2) ^ 3 +
          0.027283 * (Matrix.gram ℝ u e.val.1 e.val.2) ^ 5
      else Matrix.gram ℝ u e.val.1 e.val.2) := ⟨_, fun _ => rfl⟩
  have hround' : (∑ e : Edge n, a e * t e) ≤ ∑ e : Edge n, a e * φ e := by
    simp only [htdef, hφdef]
    exact hround
  obtain ⟨gn, hgdef⟩ : ∃ gn : Edge n → ℝ, ∀ e,
      gn e = (10920 / 38809 : ℝ) * (1 - t e * (1 + 10920 / 38809)) / 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨Mt, hMt, hMtw⟩ := matching_polytope_real_rounding
    (fun e : Edge n => (w e : ℝ) * max (gn e) 0)
    (fun e => mul_nonneg (hw e) (le_max_right _ _)) y hy0 hyload hyodd
  have hMtw' : (∑ e : Edge n, (w e : ℝ) * max (gn e) 0 * y e) ≤
      ∑ e ∈ Mt, (w e : ℝ) * max (gn e) 0 := hMtw
  obtain ⟨M', hM'def⟩ : ∃ M' : Finset (Edge n), M' = Mt.filter (fun e => 0 < gn e) := ⟨_, rfl⟩
  have hM' : ∀ e ∈ M', ∀ e' ∈ M', e ≠ e' →
      e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2 := by
    intro e he e' he' hne
    rw [hM'def] at he he'
    exact hMt e (Finset.mem_of_mem_filter _ he) e' (Finset.mem_of_mem_filter _ he') hne
  have hfilt : (∑ e ∈ M', (w e : ℝ) * gn e) = ∑ e ∈ Mt, (w e : ℝ) * max (gn e) 0 := by
    rw [hM'def, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    split_ifs with h
    · rw [max_eq_left h.le]
    · rw [max_eq_right (not_lt.mp h)]; ring
  have hC := pmatch_state_energy_lower w r hr M' hM' (195 / 197) (28 / 197) (by norm_num)
  have hC' : (∑ e : Edge n, (w e : ℝ) * ((1 - (37241 / 38809 : ℝ) ^ 2 * t e) / 2)) +
      (∑ e ∈ M', (w e : ℝ) * gn e) ≤ optimum ⟨n, w⟩ := by
    refine le_of_eq_of_le ?_ hC
    have h3 := Finset.sum_sdiff (Finset.subset_univ M')
      (f := fun e : Edge n => (w e : ℝ) * ((1 - (37241 / 38809 : ℝ) ^ 2 * t e) / 2))
    rw [← h3, add_comm (∑ e ∈ Finset.univ \ M', _), add_right_comm,
      ← Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl (fun e _ => by rw [hgdef, htdef]; ring)
    · exact Finset.sum_congr rfl (fun e _ => by rw [htdef]; ring)
  have hstep : ∀ e : Edge n,
      (w e : ℝ) * (1 / 2 + (10920 / 38809 : ℝ) / 2 * y e) - a e * t e ≤
        (w e : ℝ) * ((1 - (37241 / 38809 : ℝ) ^ 2 * t e) / 2) +
          (w e : ℝ) * max (gn e) 0 * y e := by
    intro e
    have h1 : (w e : ℝ) * gn e * y e ≤ (w e : ℝ) * max (gn e) 0 * y e :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (hw e)) (hy0 e)
    have h2 : (w e : ℝ) * (1 / 2 + (10920 / 38809 : ℝ) / 2 * y e) - a e * t e =
        (w e : ℝ) * ((1 - (37241 / 38809 : ℝ) ^ 2 * t e) / 2) + (w e : ℝ) * gn e * y e := by
      rw [hadef, hgdef]; ring
    linarith
  have hP : (∑ e : Edge n, (w e : ℝ) * (1 / 2 + (10920 / 38809 : ℝ) / 2 * y e -
      ((37241 / 38809 : ℝ) ^ 2 / 2 + (10920 / 38809 : ℝ) * (1 + 10920 / 38809) / 2 * y e) *
        φ e)) ≤ optimum ⟨n, w⟩ := by
    have e1 : (∑ e : Edge n, (w e : ℝ) * (1 / 2 + (10920 / 38809 : ℝ) / 2 * y e -
        ((37241 / 38809 : ℝ) ^ 2 / 2 +
          (10920 / 38809 : ℝ) * (1 + 10920 / 38809) / 2 * y e) * φ e)) =
        (∑ e : Edge n, (w e : ℝ) * (1 / 2 + (10920 / 38809 : ℝ) / 2 * y e)) -
          ∑ e : Edge n, a e * φ e := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun e _ => by rw [hadef]; ring)
    have e2 : (∑ e : Edge n, (w e : ℝ) * (1 / 2 + (10920 / 38809 : ℝ) / 2 * y e)) -
          ∑ e : Edge n, a e * t e ≤
        (∑ e : Edge n, (w e : ℝ) * ((1 - (37241 / 38809 : ℝ) ^ 2 * t e) / 2)) +
          ∑ e : Edge n, (w e : ℝ) * max (gn e) 0 * y e := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun e _ => hstep e)
    linarith [hround', hMtw', hfilt, hC']
  -- per-edge scalar inequality
  have hedge : ∀ e : Edge n,
      (0.6141 : ℝ) * ((1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2) ≤
        0.88 * (1 / 2 + (10920 / 38809 : ℝ) / 2 * y e -
          ((37241 / 38809 : ℝ) ^ 2 / 2 +
            (10920 / 38809 : ℝ) * (1 + 10920 / 38809) / 2 * y e) * φ e) +
        0.12 * (1 / 2 + (3 / 2) * y e) := by
    intro e
    have hs : Matrix.gram ℝ u e.val.1 e.val.2 =
        (L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e)) / 3 := hcorr e
    have hrange : -(3 : ℝ) ≤ L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e) ∧
        L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e) ≤ 1 :=
      moment_correlation_range hk L hL e.val.1 e.val.2 e.property.ne
    have hxe : F L e.val.1 e.val.2 =
        max ((1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2 - 1) 0 := rfl
    rw [hφdef, hydef]
    generalize Matrix.gram ℝ u e.val.1 e.val.2 = s at hs ⊢
    generalize F L e.val.1 e.val.2 = xe at hxe ⊢
    obtain ⟨hlo, hhi⟩ := hrange
    split_ifs with h0
    · have hσ := QuantumMaxCutEnergy.PMatch.strict_scalar_0614 (-s)
        (by linarith) (by linarith)
      have e1 : xe = max ((3 * (-s) - 1) / 2) 0 := by
        rw [hxe]; congr 1; linarith
      rw [e1]
      generalize max ((3 * (-s) - 1) / 2) 0 = m at hσ ⊢
      have e3 : (0.6141 : ℝ) * ((1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2) =
          0.6141 * ((1 + 3 * (-s)) / 2) := by
        rw [hs]; ring
      rw [e3]
      refine le_of_le_of_eq hσ ?_
      ring
    · have e1 : xe = 0 := by
        rw [hxe]; exact max_eq_right (by linarith)
      rw [e1]
      linarith
  calc (0.6141 : ℝ) * objective w L
      = ∑ e : Edge n, (w e : ℝ) *
          ((0.6141 : ℝ) * ((1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2)) := by
        unfold objective
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun e _ => by ring)
    _ ≤ ∑ e : Edge n, (w e : ℝ) *
          (0.88 * (1 / 2 + (10920 / 38809 : ℝ) / 2 * y e -
            ((37241 / 38809 : ℝ) ^ 2 / 2 +
              (10920 / 38809 : ℝ) * (1 + 10920 / 38809) / 2 * y e) * φ e) +
          0.12 * (1 / 2 + (3 / 2) * y e)) :=
        Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hedge e) (hw e))
    _ = 0.88 * (∑ e : Edge n, (w e : ℝ) * (1 / 2 + (10920 / 38809 : ℝ) / 2 * y e -
            ((37241 / 38809 : ℝ) ^ 2 / 2 +
              (10920 / 38809 : ℝ) * (1 + 10920 / 38809) / 2 * y e) * φ e)) +
          0.12 * (∑ e : Edge n, (w e : ℝ) * (1 / 2 + (3 / 2) * y e)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun e _ => by ring)
    _ ≤ optimum ⟨n, w⟩ := by linarith

/-- The pointwise bound passes to the supremum defining the relaxation value. -/
theorem value_le (I : Input) : (0.6141 : ℝ) * value 1999 I ≤ optimum I := by
  have hγ : (0 : ℝ) < 0.6141 := by norm_num
  obtain ⟨⟨L0, hL0⟩, -⟩ := value_wellposed_bounds 1999 (by norm_num) I
  have hne : ({v : ℝ | ∃ L : Word I.n → ℝ,
      Feasible 1999 L ∧ v = objective I.weights L}).Nonempty := ⟨_, L0, hL0, rfl⟩
  have hub : ∀ v ∈ {v : ℝ | ∃ L : Word I.n → ℝ, Feasible 1999 L ∧ v = objective I.weights L},
      v ≤ optimum I / 0.6141 := by
    rintro v ⟨L, hL, rfl⟩
    rw [le_div_iff₀ hγ]
    have hp : (0.6141 : ℝ) * objective I.weights L ≤ optimum I := pointwise I.n I.weights L hL
    linarith
  have hsup : value 1999 I ≤ optimum I / 0.6141 := csSup_le hne hub
  rw [le_div_iff₀ hγ] at hsup
  linarith

end QMCGap0614

end

theorem solution :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ γ : ℚ≥0,
      (0.614 : ℝ) < (γ : ℝ) ∧ (γ : ℝ) ≤ 1 ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (γ : ℝ) * QuantumMaxCutEnergy.PauliSDP.value k G ≤
          QuantumMaxCutEnergy.optimum G ∧
        QuantumMaxCutEnergy.optimum G ≤ QuantumMaxCutEnergy.PauliSDP.value k G := by
  have hγ : (((6141 : ℚ≥0) / 10000 : ℚ≥0) : ℝ) = 0.6141 := by
    push_cast; norm_num
  refine ⟨1999, by norm_num, 6141 / 10000, ?_, ?_, fun I => ⟨?_,
    QuantumMaxCutEnergy.PauliSDP.physical_state_upper_bound 1999 (by norm_num) I⟩⟩
  · rw [hγ]; norm_num
  · rw [hγ]; norm_num
  · rw [hγ]
    exact QMCGap0614.value_le I
