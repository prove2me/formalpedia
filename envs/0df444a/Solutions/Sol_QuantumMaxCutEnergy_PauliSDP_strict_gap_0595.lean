-- Prove2me | solution 1 for QuantumMaxCutEnergy.PauliSDP.strict_gap_0595
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:24:08.116412+00:00
-- url     : https://prove2.me/submissions/1638cbc8-3a64-46c1-8fc8-312525c9f676

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_strict_gap_of_pointwise
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_physical_state_upper_bound
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_moment_positive_excess_star
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_moment_triangle_bound
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_moment_correlation_range
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_exists_unit_correlation
import Theorems.Thm_QuantumMaxCutEnergy_matching_dilation_four_fifths
import Theorems.Thm_QuantumMaxCutEnergy_matching_polytope_integral_rounding
import Theorems.Thm_QuantumMaxCutEnergy_unit_bloch_assignment_energy_lower_bound
import Theorems.Thm_QuantumMaxCutEnergy_CubicMatching_lp24_strict_scalar
import Theorems.Thm_QuantumMaxCutEnergy_rank3_gaussian_rounding_cubic
import Theorems.Thm_QuantumMaxCutEnergy_matching_state_energy_lower
import Mathlib
open scoped BigOperators

noncomputable section

namespace QMCGap0595
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

theorem G_range (L : Word n → ℝ) (hL : Feasible 2 L) (i j : Fin n) (hij : i ≠ j) :
    0 ≤ G L i j ∧ G L i j ≤ 2 := by
  have h := moment_correlation_range (le_refl 2) L hL i j hij
  unfold G
  constructor <;> linarith [h.1, h.2]

/-- The positive excess of a pair value over one. -/
def F (L : Word n → ℝ) (i j : Fin n) : ℝ := max (G L i j - 1) 0

theorem F_comm (L : Word n → ℝ) (i j : Fin n) : F L i j = F L j i := by
  unfold F; rw [G_comm]

theorem F_nonneg (L : Word n → ℝ) (i j : Fin n) : 0 ≤ F L i j := le_max_right _ _

/-- The cubic rounding curve. -/
def phi (t : ℝ) : ℝ := if t ≤ 0 then 0.8488 * t + 0.08488 * t ^ 3 else t

theorem three_excess (a b c : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (h : a + b + c ≤ 3) (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2) :
    max (a - 1) 0 + max (b - 1) 0 + max (c - 1) 0 ≤ 1 := by
  rcases max_cases (a - 1) 0 with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
  rcases max_cases (b - 1) 0 with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
  rcases max_cases (c - 1) 0 with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
  rw [h1, h2, h3] <;> linarith

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

theorem exists_sorted_triple (S : Finset (Fin n)) (h : S.card = 3) :
    ∃ a b c : Fin n, a < b ∧ b < c ∧ S = {a, b, c} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp h
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  · exact ⟨x, y, z, h1, h3, rfl⟩
  · exact ⟨x, z, y, h2, h3, by
      ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact absurd (h2.trans (h1.trans h3)) (lt_irrefl _)
  · exact ⟨z, x, y, h2, h1, by
      ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact ⟨y, x, z, h1, h2, by
      ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact absurd (h1.trans (h2.trans h3)) (lt_irrefl _)
  · exact ⟨y, z, x, h3, h2, by
      ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact ⟨z, y, x, h3, h1, by
      ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩

theorem tri_filter (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    (Finset.univ.filter (fun e : Edge n =>
      e.val.1 ∈ ({a, b, c} : Finset (Fin n)) ∧ e.val.2 ∈ ({a, b, c} : Finset (Fin n)))) =
      {⟨(a, b), hab⟩, ⟨(a, c), hab.trans hbc⟩, ⟨(b, c), hbc⟩} := by
  ext ⟨⟨i, j⟩, hij⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩
    · exact absurd hij (lt_irrefl _)
    · simp
    · simp
    · exact absurd hij (lt_asymm hab)
    · exact absurd hij (lt_irrefl _)
    · simp
    · exact absurd hij (lt_asymm (hab.trans hbc))
    · exact absurd hij (lt_asymm hbc)
    · exact absurd hij (lt_irrefl _)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

theorem tri_sum_le (L : Word n → ℝ) (hL : Feasible 2 L) (S : Finset (Fin n))
    (hS : S.card = 3) :
    (∑ e ∈ Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S),
      F L e.val.1 e.val.2) ≤ 1 := by
  obtain ⟨a, b, c, hab, hbc, rfl⟩ := exists_sorted_triple S hS
  have hac := hab.trans hbc
  rw [tri_filter a b c hab hbc, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · have ht := moment_triangle_bound (le_refl 2) L hL a b c hab.ne hac.ne hbc.ne
    have r1 := G_range L hL a b hab.ne
    have r2 := G_range L hL a c hac.ne
    have r3 := G_range L hL b c hbc.ne
    have h3 := three_excess (G L a b) (G L a c) (G L b c) r1.1 r2.1 r3.1 ht r1.2 r2.2 r3.2
    show F L a b + (F L a c + F L b c) ≤ 1
    unfold F
    linarith
  · simp [hab.ne]
  · simp [hbc.ne, hab.ne]

theorem pointwise (n : ℕ) (w : Weights n) (L : Word n → ℝ) (hL : Feasible 2 L) :
    (0.5955 : ℝ) * objective w L ≤ optimum ⟨n, w⟩ := by
  have hk : (2 : ℕ) ≤ 2 := le_rfl
  have hw : ∀ e : Edge n, (0 : ℝ) ≤ (w e : ℝ) := fun e => NNRat.cast_nonneg _
  -- matching side
  have hx0 : ∀ e : Edge n, 0 ≤ F L e.val.1 e.val.2 := fun e => F_nonneg L _ _
  have hload : ∀ v : Fin n,
      (∑ e : Edge n, if v = e.val.1 ∨ v = e.val.2 then F L e.val.1 e.val.2 else 0) ≤ 1 := by
    intro v
    rw [star_sum (F L) (F_comm L) v]
    exact moment_positive_excess_star hk L hL v (Finset.univ.erase v) (by simp)
  have htri : ∀ S : Finset (Fin n), Odd S.card → S.card ≤ 4 →
      (∑ e ∈ (Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S)),
        F L e.val.1 e.val.2) ≤ ((S.card : ℝ) - 1) / 2 := by
    intro S hodd h4
    have hc : S.card = 1 ∨ S.card = 3 := by
      obtain ⟨k, hk⟩ := hodd; omega
    rcases hc with hc | hc
    · rw [hc]
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      rw [Finset.sum_eq_zero]
      · norm_num
      · intro e he
        exfalso
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at he
        exact absurd e.property (by rw [he.1, he.2]; exact lt_irrefl _)
    · rw [hc]
      have := tri_sum_le L hL S hc
      norm_num
      exact this
  obtain ⟨hy0, hyload, hyodd⟩ :=
    matching_dilation_four_fifths (fun e : Edge n => F L e.val.1 e.val.2) hx0 hload htri
  obtain ⟨M, hM, hMw⟩ := matching_polytope_integral_rounding w
    (fun e : Edge n => ((4 : ℝ) / 5) * F L e.val.1 e.val.2) hy0 hyload hyodd
  have hMw' : (∑ e : Edge n, (w e : ℝ) * (((4 : ℝ) / 5) * F L e.val.1 e.val.2)) ≤
      ∑ e ∈ M, (w e : ℝ) := hMw
  have hA := matching_state_energy_lower w M hM
  -- product side
  obtain ⟨u, hu, hcorr⟩ := exists_unit_correlation hk L hL
  obtain ⟨r, hr, hround⟩ := rank3_gaussian_rounding_cubic n w (Matrix.gram ℝ u)
    (Matrix.posSemidef_gram ℝ u)
    (fun i => by rw [Matrix.gram_apply, real_inner_self_eq_norm_sq, hu i]; norm_num)
  have hround' : (∑ e : Edge n, (w e : ℝ) * (∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) ≤
      ∑ e : Edge n, (w e : ℝ) * phi (Matrix.gram ℝ u e.val.1 e.val.2) := hround
  have hB : (∑ e : Edge n, (w e : ℝ) *
      (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2) ≤ optimum ⟨n, w⟩ :=
    unit_bloch_assignment_energy_lower_bound ⟨n, w⟩ r hr
  have hB' : ((∑ e : Edge n, (w e : ℝ)) -
      ∑ e : Edge n, (w e : ℝ) * (∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) / 2 ≤
      optimum ⟨n, w⟩ := by
    refine le_of_eq_of_le ?_ hB
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  -- per-edge scalar inequality
  have hedge : ∀ e : Edge n,
      (0.5955 : ℝ) * ((1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2) ≤
        0.672 * ((1 - phi (Matrix.gram ℝ u e.val.1 e.val.2)) / 2) +
        0.328 * (1 / 2 + (3 / 2) * (((4 : ℝ) / 5) * F L e.val.1 e.val.2)) := by
    intro e
    have hs : Matrix.gram ℝ u e.val.1 e.val.2 =
        (L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e)) / 3 := hcorr e
    have hrange : -(3 : ℝ) ≤ L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e) ∧
        L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e) ≤ 1 :=
      moment_correlation_range hk L hL e.val.1 e.val.2 e.property.ne
    have hxe : F L e.val.1 e.val.2 =
        max ((1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2 - 1) 0 := rfl
    generalize Matrix.gram ℝ u e.val.1 e.val.2 = s at hs ⊢
    generalize F L e.val.1 e.val.2 = xe at hxe ⊢
    obtain ⟨hlo, hhi⟩ := hrange
    unfold phi
    split_ifs with h0
    · have hσ := QuantumMaxCutEnergy.CubicMatching.lp24_strict_scalar (-s)
        (by linarith) (by linarith)
      have e1 : xe = max ((3 * (-s) - 1) / 2) 0 := by
        rw [hxe]; congr 1; linarith
      have e2 : (-s) ^ 3 = -s ^ 3 := by ring
      rw [e2] at hσ
      rw [e1]
      linarith
    · have e1 : xe = 0 := by
        rw [hxe]; exact max_eq_right (by linarith)
      rw [e1]
      linarith
  have hsum : (0.5955 : ℝ) * objective w L ≤
      0.672 * (((∑ e : Edge n, (w e : ℝ)) -
        ∑ e : Edge n, (w e : ℝ) * phi (Matrix.gram ℝ u e.val.1 e.val.2)) / 2) +
      0.328 * (((∑ e : Edge n, (w e : ℝ)) +
        3 * ∑ e : Edge n, (w e : ℝ) * (((4 : ℝ) / 5) * F L e.val.1 e.val.2)) / 2) := by
    calc (0.5955 : ℝ) * objective w L
        = ∑ e : Edge n, (w e : ℝ) *
            ((0.5955 : ℝ) * ((1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2)) := by
          unfold objective
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun e _ => by ring)
      _ ≤ ∑ e : Edge n, (w e : ℝ) *
            (0.672 * ((1 - phi (Matrix.gram ℝ u e.val.1 e.val.2)) / 2) +
              0.328 * (1 / 2 + (3 / 2) * (((4 : ℝ) / 5) * F L e.val.1 e.val.2))) :=
          Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hedge e) (hw e))
      _ = _ := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
            Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun e _ => by ring)
  linarith [hA, hB', hround', hMw', hsum]

end QMCGap0595

end

theorem solution :
    ∃ γ : ℚ≥0, (0.595 : ℝ) < (γ : ℝ) ∧ (γ : ℝ) ≤ 1 ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (γ : ℝ) * QuantumMaxCutEnergy.PauliSDP.value 2 G ≤
          QuantumMaxCutEnergy.optimum G ∧
        QuantumMaxCutEnergy.optimum G ≤ QuantumMaxCutEnergy.PauliSDP.value 2 G := by
  have hγ : (((1191 : ℚ≥0) / 2000 : ℚ≥0) : ℝ) = 0.5955 := by
    push_cast; norm_num
  refine QuantumMaxCutEnergy.PauliSDP.strict_gap_of_pointwise (1191 / 2000) ?_ ?_ ?_ ?_
  · rw [hγ]; norm_num
  · rw [hγ]; norm_num
  · intro n w L hL
    rw [hγ]
    exact QMCGap0595.pointwise n w L hL
  · exact fun G => QuantumMaxCutEnergy.PauliSDP.physical_state_upper_bound 2 le_rfl G
