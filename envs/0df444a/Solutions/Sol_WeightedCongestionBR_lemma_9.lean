-- Prove2me | solution 1 for WeightedCongestionBR.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:47:48.08221+00:00
-- url     : https://prove2.me/submissions/b29e2c82-bb1c-435f-845e-8bb89181300a

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_WeightedCongestionBR_IsGroupEq
import Definitions.Def_WeightedCongestionBR_genGolden
import Definitions.Def_WeightedCongestionBR_partialPot
import Definitions.Def_WeightedCongestionBR_alphaC
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace Aux9gc

noncomputable def gcost {n r : ℕ} (G : HarksKlimm.Consistency.Game n r) (R : Finset (Fin n))
    (s : G.Profile) : ℝ :=
  ∑ u ∈ R, privateCost G s u

end Aux9gc


namespace Aux9a

open WeightedCongestionBR Aux9gc

theorem pair_term (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (k j : ℕ) :
    y ^ k * x ^ j + y ^ j * x ^ k ≤ x ^ (k + j) + y ^ (k + j) := by
  have h1 : x ^ k ≤ y ^ k := pow_le_pow_left₀ hx hxy k
  have h2 : x ^ j ≤ y ^ j := pow_le_pow_left₀ hx hxy j
  rw [pow_add, pow_add]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

theorem trap (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (ν : ℕ) :
    2 * ∑ k ∈ Finset.range (ν + 1), y ^ k * x ^ (ν - k) ≤ ((ν : ℝ) + 1) * (x ^ ν + y ^ ν) := by
  have hrefl : ∑ k ∈ Finset.range (ν + 1), y ^ k * x ^ (ν - k)
      = ∑ k ∈ Finset.range (ν + 1), y ^ (ν - k) * x ^ k := by
    rw [← Finset.sum_range_reflect (fun k => y ^ k * x ^ (ν - k)) (ν + 1)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k < ν + 1 := Finset.mem_range.mp hk
    have e1 : ν + 1 - 1 - k = ν - k := by omega
    have e3 : ν - (ν - k) = k := by omega
    simp only [e1, e3]
  calc 2 * ∑ k ∈ Finset.range (ν + 1), y ^ k * x ^ (ν - k)
      = ∑ k ∈ Finset.range (ν + 1), y ^ k * x ^ (ν - k)
        + ∑ k ∈ Finset.range (ν + 1), y ^ (ν - k) * x ^ k := by rw [← hrefl]; ring
    _ = ∑ k ∈ Finset.range (ν + 1), (y ^ k * x ^ (ν - k) + y ^ (ν - k) * x ^ k) :=
        (Finset.sum_add_distrib).symm
    _ ≤ ∑ _k ∈ Finset.range (ν + 1), (x ^ ν + y ^ ν) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hk' : k < ν + 1 := Finset.mem_range.mp hk
        have h := pair_term x y hx hxy k (ν - k)
        have e : k + (ν - k) = ν := by omega
        rw [e] at h
        exact h
    _ = ((ν : ℝ) + 1) * (x ^ ν + y ^ ν) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem term_bounds (d ν : ℕ) (hν : ν ≤ d) (x w : ℝ) (hx : 0 ≤ x) (hw : 1 ≤ w) :
    w * (x + w) ^ ν ≤ ((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
        - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν) ∧
      ((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
        - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν) ≤ ((d : ℝ) + 1) * w * (x + w) ^ ν := by
  obtain ⟨y, hy⟩ : ∃ y, y = x + w := ⟨_, rfl⟩
  rw [← hy]
  have hxy : x ≤ y := by rw [hy]; linarith
  have hy0 : 0 ≤ y := le_trans hx hxy
  have hgeom := geom_sum₂_mul y x (ν + 1)
  simp only [Nat.add_sub_cancel] at hgeom
  obtain ⟨E, hE⟩ : ∃ E, E = ∑ i ∈ Finset.range (ν + 1), y ^ i * x ^ (ν - i) := ⟨_, rfl⟩
  rw [← hE] at hgeom
  have hyx : y - x = w := by rw [hy]; ring
  rw [hyx] at hgeom
  have hEge : y ^ ν ≤ E := by
    have h := Finset.single_le_sum (f := fun i => y ^ i * x ^ (ν - i)) (s := Finset.range (ν + 1))
      (fun i _ => mul_nonneg (pow_nonneg hy0 _) (pow_nonneg hx _)) (Finset.self_mem_range_succ ν)
    simp only [Nat.sub_self, pow_zero, mul_one] at h
    rw [hE]
    exact h
  have hEle : 2 * E ≤ ((ν : ℝ) + 1) * (x ^ ν + y ^ ν) := by rw [hE]; exact trap x y hx hxy ν
  have hxν : x ^ ν ≤ y ^ ν := pow_le_pow_left₀ hx hxy ν
  have hw0 : 0 ≤ w := by linarith
  have hc : (0 : ℝ) ≤ (ν : ℝ) + 1 := by positivity
  have hdν : (ν : ℝ) ≤ d := by exact_mod_cast hν
  have hyν : 0 ≤ y ^ ν := pow_nonneg hy0 ν
  constructor
  · have h1 : 0 ≤ w * (E - y ^ ν) := mul_nonneg hw0 (sub_nonneg.mpr hEge)
    have h2 : 0 ≤ ((ν : ℝ) + 1) * (y ^ ν - x ^ ν) := mul_nonneg hc (sub_nonneg.mpr hxν)
    nlinarith
  · have h1 : w * (2 * E) ≤ w * (((ν : ℝ) + 1) * (x ^ ν + y ^ ν)) :=
      mul_le_mul_of_nonneg_left hEle hw0
    have h2 : 0 ≤ (w - 1) * (((ν : ℝ) + 1) * (y ^ ν - x ^ ν)) :=
      mul_nonneg (by linarith) (mul_nonneg hc (sub_nonneg.mpr hxν))
    have h3 : 0 ≤ ((d : ℝ) - ν) * (w * y ^ ν) :=
      mul_nonneg (by linarith) (mul_nonneg hw0 hyν)
    nlinarith

theorem eval_split (P : Polynomial ℝ) (z : ℝ) :
    P.eval z = P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * z ^ ν := by
  rw [Polynomial.eval_eq_sum_range, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < P.natDegree + 1), Finset.Ico_add_one_right_eq_Icc]
  simp only [pow_zero, mul_one, zero_add]


theorem lemma4 (d : ℕ) (hd : 1 ≤ d) (P : Polynomial ℝ) (hP : P.natDegree ≤ d ∧ ∀ j, 0 ≤ P.coeff j) (x w : ℝ) (hx : 0 ≤ x)
    (hw : 1 ≤ w) :
    w * P.eval (x + w) ≤ phiPoly P (x + w) - phiPoly P x ∧
      phiPoly P (x + w) - phiPoly P x ≤ alphaC d * w * P.eval (x + w) := by
  obtain ⟨hdeg, hcoef⟩ := hP
  unfold phiPoly alphaC
  rw [eval_split]
  have hdiff : (∑ ν ∈ Finset.Icc 1 P.natDegree,
        P.coeff ν * ((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν))
      - (∑ ν ∈ Finset.Icc 1 P.natDegree,
        P.coeff ν * (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν))
      = ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν *
        (((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
          - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    ring
  have eL : w * (P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (x + w) ^ ν)
      = w * P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (w * (x + w) ^ ν) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    ring
  have eU : ((d : ℝ) + 1) * w * (P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (x + w) ^ ν)
      = ((d : ℝ) + 1) * w * P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree,
          P.coeff ν * (((d : ℝ) + 1) * w * (x + w) ^ ν) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    ring
  have hsumL : ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (w * (x + w) ^ ν)
      ≤ ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν *
        (((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
          - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν)) := by
    refine Finset.sum_le_sum (fun ν hν => ?_)
    have hνd : ν ≤ d := le_trans (Finset.mem_Icc.mp hν).2 hdeg
    exact mul_le_mul_of_nonneg_left (term_bounds d ν hνd x w hx hw).1 (hcoef ν)
  have hsumU : ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν *
        (((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
          - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν))
      ≤ ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (((d : ℝ) + 1) * w * (x + w) ^ ν) := by
    refine Finset.sum_le_sum (fun ν hν => ?_)
    have hνd : ν ≤ d := le_trans (Finset.mem_Icc.mp hν).2 hdeg
    exact mul_le_mul_of_nonneg_left (term_bounds d ν hνd x w hx hw).2 (hcoef ν)
  have ha0 : 0 ≤ P.coeff 0 := hcoef 0
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hw0 : 0 ≤ w := by linarith
  have hprod : 0 ≤ (d : ℝ) * w * P.coeff 0 := mul_nonneg (mul_nonneg hd0 hw0) ha0
  have hlin0 : P.coeff 0 * (x + w) - P.coeff 0 * x = w * P.coeff 0 := by ring
  have hlin1 : ((d : ℝ) + 1) * w * P.coeff 0 = (d : ℝ) * w * P.coeff 0 + w * P.coeff 0 := by ring
  constructor
  · rw [eL]
    linarith
  · rw [eU]
    linarith

/-- Facility-level bounds, allowing `w = 0`. -/
theorem fac (d : ℕ) (hd : 1 ≤ d) (P : Polynomial ℝ) (hP : P.natDegree ≤ d ∧ ∀ j, 0 ≤ P.coeff j) (x w : ℝ) (hx : 0 ≤ x)
    (hw : w = 0 ∨ 1 ≤ w) :
    w * P.eval (x + w) ≤ phiPoly P (x + w) - phiPoly P x ∧
      phiPoly P (x + w) - phiPoly P x ≤ alphaC d * w * P.eval (x + w) := by
  rcases hw with h0 | h1
  · subst h0
    simp
  · exact lemma4 d hd P hP x w hx h1

theorem costPoly_eq {n r : ℕ} (G : Game n r) (e : Fin r) (P : Polynomial ℝ)
    (hP : ∀ x : ℝ≥0, G.cost e x = P.eval (x : ℝ)) : costPoly G e = P := by
  have hex : ∃ P : Polynomial ℝ, ∀ x : ℝ≥0, G.cost e x = P.eval (x : ℝ) := ⟨P, hP⟩
  unfold costPoly
  rw [dif_pos hex]
  have hQ := Classical.choose_spec hex
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ici_infinite (0 : ℝ)).mono
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := hx
  show Polynomial.eval x (Classical.choose hex) = Polynomial.eval x P
  have h1 := hQ ⟨x, hx0⟩
  have h2 := hP ⟨x, hx0⟩
  exact h1.symm.trans h2

theorem load_eq {n r : ℕ} (G : Game n r) (s : G.Profile) (e : Fin r) :
    ((load G s e : ℝ≥0) : ℝ) = groupLoad G s Finset.univ e := by
  unfold load groupLoad
  rw [NNReal.coe_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp

theorem groupLoad_split {n r : ℕ} (G : Game n r) (s : G.Profile) (R : Finset (Fin n)) (e : Fin r) :
    groupLoad G s Finset.univ e = groupLoad G s Rᶜ e + groupLoad G s R e := by
  unfold groupLoad
  rw [← Finset.sum_add_sum_compl R]
  ring

theorem groupLoad_nonneg {n r : ℕ} (G : Game n r) (s : G.Profile) (R : Finset (Fin n)) (e : Fin r) :
    0 ≤ groupLoad G s R e := by
  unfold groupLoad
  refine Finset.sum_nonneg (fun u _ => ?_)
  split_ifs
  · exact NNReal.coe_nonneg _
  · exact le_rfl

theorem groupLoad_cases {n r : ℕ} (G : Game n r) (hw : ∀ u, 1 ≤ G.demand u) (s : G.Profile)
    (R : Finset (Fin n)) (e : Fin r) :
    groupLoad G s R e = 0 ∨ 1 ≤ groupLoad G s R e := by
  by_cases h : ∃ u ∈ R, e ∈ (s u).val
  · right
    obtain ⟨u, hu, he⟩ := h
    unfold groupLoad
    have hle := Finset.single_le_sum (f := fun u => if e ∈ (s u).val then (G.demand u : ℝ) else 0)
      (fun u _ => by
        show 0 ≤ (if e ∈ (s u).val then (G.demand u : ℝ) else 0)
        split_ifs
        · exact NNReal.coe_nonneg _
        · exact le_rfl) hu
    simp only [he, ↓reduceIte] at hle
    have h1 : (1 : ℝ) ≤ (G.demand u : ℝ) := by exact_mod_cast hw u
    linarith
  · left
    push_neg at h
    unfold groupLoad
    refine Finset.sum_eq_zero (fun u hu => ?_)
    rw [if_neg (h u hu)]

theorem groupCost_eq {n r : ℕ} (G : Game n r) (R : Finset (Fin n)) (s : G.Profile) :
    gcost G R s = ∑ e : Fin r, groupLoad G s R e * G.cost e (load G s e) := by
  unfold gcost privateCost groupLoad
  simp_rw [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem_eq]

theorem mainL {n r : ℕ} (G : Game n r) (d : ℕ) (hd : 1 ≤ d)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u)
    (R : Finset (Fin n)) (s : G.Profile) :
    gcost G R s ≤ partialPot G R s ∧ partialPot G R s ≤ alphaC d * gcost G R s := by
  have hPf : ∀ e : Fin r, ∃ P : Polynomial ℝ, (P.natDegree ≤ d ∧ ∀ j, 0 ≤ P.coeff j) ∧ costPoly G e = P ∧
      ∀ x : ℝ≥0, G.cost e x = P.eval (x : ℝ) := by
    intro e
    obtain ⟨P, hdeg, hcoef, hcost⟩ := hG e
    exact ⟨P, ⟨hdeg, hcoef⟩, costPoly_eq G e P hcost, hcost⟩
  choose P hPd hcP hcost using hPf
  have hC : gcost G R s = ∑ e : Fin r,
      groupLoad G s R e * (P e).eval (groupLoad G s Rᶜ e + groupLoad G s R e) := by
    rw [groupCost_eq]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [hcost e, load_eq, groupLoad_split G s R e]
  have hΦ : partialPot G R s = ∑ e : Fin r,
      (phiPoly (P e) (groupLoad G s Rᶜ e + groupLoad G s R e) - phiPoly (P e) (groupLoad G s Rᶜ e)) := by
    unfold partialPot subgamePot
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [hcP e, groupLoad_split G s R e]
  have hfac := fun e : Fin r => fac d hd (P e) (hPd e) (groupLoad G s Rᶜ e) (groupLoad G s R e)
    (groupLoad_nonneg G s Rᶜ e) (groupLoad_cases G hw s R e)
  rw [hC, hΦ]
  constructor
  · exact Finset.sum_le_sum (fun e _ => (hfac e).1)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun e _ => ?_)
    have := (hfac e).2
    calc _ ≤ alphaC d * groupLoad G s R e * (P e).eval (groupLoad G s Rᶜ e + groupLoad G s R e) :=
          this
      _ = _ := by ring

end Aux9a


namespace Aux9b

open WeightedCongestionBR Aux9gc

/-- Weighted AM-GM: `(N+1) u v^N ≤ u^(N+1) + N v^(N+1)`. -/
theorem amgm (N : ℕ) (hN : 1 ≤ N) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ((N : ℝ) + 1) * u * v ^ N ≤ u ^ (N + 1) + (N : ℝ) * v ^ (N + 1) := by
  rcases hv.lt_or_eq with hv | hv
  · obtain ⟨t, ht⟩ : ∃ t : ℝ, t = u / v := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg hu hv.le
    have hu' : u = t * v := by rw [ht, div_mul_cancel₀ u hv.ne']
    subst hu'
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ t - 1 by linarith) (N + 1)
    rw [show (1 : ℝ) + (t - 1) = t by ring] at hb
    push_cast at hb
    have key := mul_le_mul_of_nonneg_right hb (pow_nonneg hv.le (N + 1))
    rw [mul_pow, pow_succ v N]
    rw [pow_succ v N] at key
    linarith [key]
  · subst hv
    rw [zero_pow (show N ≠ 0 by omega), zero_pow (show N + 1 ≠ 0 by omega)]
    simp only [mul_zero, add_zero]
    exact pow_nonneg hu _

/-- Convexity: `Φ^N (x+y)^(N+1) ≤ Φ^N P^N y^(N+1) + P^N x^(N+1)` with `P = Φ + 1`. -/
theorem conv (N : ℕ) (Φ : ℝ) (hΦ : 0 < Φ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Φ ^ N * (x + y) ^ (N + 1) ≤ Φ ^ N * (Φ + 1) ^ N * y ^ (N + 1) + (Φ + 1) ^ N * x ^ (N + 1) := by
  have hP : 0 < Φ + 1 := by linarith
  have hΦne : Φ ≠ 0 := hΦ.ne'
  have hPne : Φ + 1 ≠ 0 := hP.ne'
  have hconv := (convexOn_pow (𝕜 := ℝ) (N + 1)).2
    (Set.mem_Ici.mpr (mul_nonneg hP.le hy))
    (Set.mem_Ici.mpr (div_nonneg (mul_nonneg hP.le hx) hΦ.le))
    (div_nonneg zero_le_one hP.le) (div_nonneg hΦ.le hP.le)
    (show 1 / (Φ + 1) + Φ / (Φ + 1) = 1 by field_simp; try ring)
  simp only [smul_eq_mul] at hconv
  have e1 : 1 / (Φ + 1) * ((Φ + 1) * y) + Φ / (Φ + 1) * ((Φ + 1) * x / Φ) = x + y := by
    field_simp
    try ring
  rw [e1] at hconv
  have e2 : Φ ^ N * (1 / (Φ + 1) * ((Φ + 1) * y) ^ (N + 1) +
      Φ / (Φ + 1) * ((Φ + 1) * x / Φ) ^ (N + 1)) =
      Φ ^ N * (Φ + 1) ^ N * y ^ (N + 1) + (Φ + 1) ^ N * x ^ (N + 1) := by
    have hΦ' : Φ ≠ 0 := hΦ.ne'
    have hP' : Φ + 1 ≠ 0 := hP.ne'
    rw [mul_pow, div_pow, mul_pow]
    field_simp
    try ring
  rw [← e2]
  exact mul_le_mul_of_nonneg_left hconv (pow_nonneg hΦ.le N)

/-- The degree-`(n+1)` two-variable inequality with the tangent coefficients. -/
theorem degD (n : ℕ) (Φ : ℝ) (hΦ : 0 < Φ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y * (x + y) ^ (n + 1) ≤
      (Φ + 1) ^ n * ((Φ + 1) + ((n : ℝ) + 1)) / ((n : ℝ) + 2) * (y * y ^ (n + 1)) +
      ((n : ℝ) + 1) * (Φ + 1) ^ n / (((n : ℝ) + 2) * Φ ^ (n + 1)) * (x * x ^ (n + 1)) := by
  have hP : 0 < Φ + 1 := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have A := amgm (n + 1) (by omega) ((Φ + 1) * y) (x + y) (mul_nonneg hP.le hy) (by linarith)
  push_cast at A
  have Cv := conv (n + 1) Φ hΦ x y hx hy
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((n : ℝ) + 2) * (Φ + 1) * Φ ^ (n + 1) := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have step : K * (y * (x + y) ^ (n + 1)) ≤
      K * ((Φ + 1) ^ n * ((Φ + 1) + ((n : ℝ) + 1)) / ((n : ℝ) + 2) * (y * y ^ (n + 1)) +
      ((n : ℝ) + 1) * (Φ + 1) ^ n / (((n : ℝ) + 2) * Φ ^ (n + 1)) * (x * x ^ (n + 1))) := by
    have A' := mul_le_mul_of_nonneg_left A (pow_nonneg hΦ.le (n + 1))
    have Cv' := mul_le_mul_of_nonneg_left Cv hn1
    calc K * (y * (x + y) ^ (n + 1))
        = Φ ^ (n + 1) * (((n : ℝ) + 1 + 1) * ((Φ + 1) * y) * (x + y) ^ (n + 1)) := by
          rw [hK]; ring
      _ ≤ Φ ^ (n + 1) * (((Φ + 1) * y) ^ (n + 1 + 1) + ((n : ℝ) + 1) * (x + y) ^ (n + 1 + 1)) := by
          linarith [A']
      _ = Φ ^ (n + 1) * ((Φ + 1) * y) ^ (n + 1 + 1) +
            ((n : ℝ) + 1) * (Φ ^ (n + 1) * (x + y) ^ (n + 1 + 1)) := by ring
      _ ≤ Φ ^ (n + 1) * ((Φ + 1) * y) ^ (n + 1 + 1) +
            ((n : ℝ) + 1) * (Φ ^ (n + 1) * (Φ + 1) ^ (n + 1) * y ^ (n + 1 + 1) +
              (Φ + 1) ^ (n + 1) * x ^ (n + 1 + 1)) := by linarith
      _ = K * ((Φ + 1) ^ n * ((Φ + 1) + ((n : ℝ) + 1)) / ((n : ℝ) + 2) * (y * y ^ (n + 1)) +
            ((n : ℝ) + 1) * (Φ + 1) ^ n / (((n : ℝ) + 2) * Φ ^ (n + 1)) * (x * x ^ (n + 1))) := by
          have hΦ' : Φ ≠ 0 := hΦ.ne'
          have hn2' : (n : ℝ) + 2 ≠ 0 := hn2.ne'
          rw [hK]
          simp only [mul_pow]
          field_simp
          try ring
  exact le_of_mul_le_mul_left step hK0

/-- Lower-degree version obtained from the top-degree one. -/
theorem base (d j : ℕ) (hj : j ≤ d) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (D : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y * (x + y) ^ d ≤ l * (y * y ^ d) + m * (x * x ^ d))
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y * (x + y) ^ j ≤ l * (y * y ^ j) + m * (x * x ^ j) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = j + e := ⟨d - j, by omega⟩
  rcases (show (0 : ℝ) ≤ x + y by linarith).lt_or_eq with hw | hw
  · have D' := D x y hx hy
    have hyw : y ^ e ≤ (x + y) ^ e := pow_le_pow_left₀ hy (by linarith) e
    have hxw : x ^ e ≤ (x + y) ^ e := pow_le_pow_left₀ hx (by linarith) e
    have a1 : y * y ^ (j + e) ≤ y * y ^ j * (x + y) ^ e := by
      rw [pow_add, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hyw (by positivity)
    have a2 : x * x ^ (j + e) ≤ x * x ^ j * (x + y) ^ e := by
      rw [pow_add, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hxw (by positivity)
    have b1 := mul_le_mul_of_nonneg_left a1 hl
    have b2 := mul_le_mul_of_nonneg_left a2 hm
    have step : (x + y) ^ e * (y * (x + y) ^ j) ≤
        (x + y) ^ e * (l * (y * y ^ j) + m * (x * x ^ j)) := by
      calc (x + y) ^ e * (y * (x + y) ^ j) = y * (x + y) ^ (j + e) := by ring
        _ ≤ l * (y * y ^ (j + e)) + m * (x * x ^ (j + e)) := D'
        _ ≤ l * (y * y ^ j * (x + y) ^ e) + m * (x * x ^ j * (x + y) ^ e) := by linarith
        _ = (x + y) ^ e * (l * (y * y ^ j) + m * (x * x ^ j)) := by ring
    exact le_of_mul_le_mul_left step (pow_pos hw e)
  · have hy0 : y = 0 := by linarith
    have hx0 : x = 0 := by linarith
    subst hy0
    subst hx0
    simp

/-- Monomial version with the extra variable `z`, by binomial expansion in `z`. -/
theorem monoL (d k : ℕ) (hk : k ≤ d) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (D : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y * (x + y) ^ d ≤ l * (y * y ^ d) + m * (x * x ^ d))
    (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    y * (z + x + y) ^ k ≤ l * y * (z + y) ^ k + m * x * (z + x) ^ k := by
  have e1 : z + x + y = z + (x + y) := by ring
  rw [e1, add_pow z (x + y) k, add_pow z y k, add_pow z x k, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hb := base d (k - i) (by omega) l m hl hm D x y hx hy
  have hzc : 0 ≤ z ^ i * ((k.choose i : ℕ) : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hb hzc
  calc y * (z ^ i * (x + y) ^ (k - i) * ((k.choose i : ℕ) : ℝ))
      = z ^ i * ((k.choose i : ℕ) : ℝ) * (y * (x + y) ^ (k - i)) := by ring
    _ ≤ z ^ i * ((k.choose i : ℕ) : ℝ) * (l * (y * y ^ (k - i)) + m * (x * x ^ (k - i))) := this
    _ = l * y * (z ^ i * y ^ (k - i) * ((k.choose i : ℕ) : ℝ)) +
          m * x * (z ^ i * x ^ (k - i) * ((k.choose i : ℕ) : ℝ)) := by ring

/-- Polynomial version. -/
theorem polyL (d : ℕ) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (D : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y * (x + y) ^ d ≤ l * (y * y ^ d) + m * (x * x ^ d))
    (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (f : Polynomial ℝ) (hf : f.natDegree ≤ d ∧ ∀ j, 0 ≤ f.coeff j) :
    y * f.eval (z + x + y) ≤ l * y * f.eval (z + y) + m * x * f.eval (z + x) := by
  have hlt : f.natDegree < d + 1 := Nat.lt_succ_of_le hf.1
  simp only [Polynomial.eval_eq_sum_range' hlt]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hmo := monoL d k hkd l m hl hm D x y z hx hy hz
  have hc := hf.2 k
  have := mul_le_mul_of_nonneg_left hmo hc
  calc y * (f.coeff k * (z + x + y) ^ k) = f.coeff k * (y * (z + x + y) ^ k) := by ring
    _ ≤ f.coeff k * (l * y * (z + y) ^ k + m * x * (z + x) ^ k) := this
    _ = l * y * (f.coeff k * (z + y) ^ k) + m * x * (f.coeff k * (z + x) ^ k) := by ring

theorem root_exists (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ ρ * (r + 1) ^ N = r ^ (N + 1) := by
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ρ * 2 ^ N + 1 := ⟨_, rfl⟩
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hX0 : 0 ≤ X := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) (Set.Icc 0 X) := by
    fun_prop
  have hiv := intermediate_value_Icc hX0 hcont
  have hg0 : (fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) 0 = -ρ := by simp
  have hgX : 0 ≤ (fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) X := by
    show 0 ≤ X ^ (N + 1) - ρ * (X + 1) ^ N
    have h1 : (X + 1) ^ N ≤ (2 * X) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    rw [mul_pow] at h1
    have hXN : 0 < X ^ N := by positivity
    have h3 : ρ * 2 ^ N ≤ X := by rw [hX]; linarith
    have h4 : ρ * 2 ^ N * X ^ N ≤ X * X ^ N := mul_le_mul_of_nonneg_right h3 hXN.le
    have h5 := mul_le_mul_of_nonneg_left h1 hρ.le
    rw [pow_succ]
    linarith
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) 0)
      ((fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) X) := by
    rw [hg0]; exact ⟨by linarith, hgX⟩
  obtain ⟨r, ⟨hr0, _⟩, hr⟩ := hiv hmem
  have hr' : r ^ (N + 1) - ρ * (r + 1) ^ N = 0 := hr
  refine ⟨r, ?_, by linarith⟩
  rcases hr0.lt_or_eq with h | h
  · exact h
  · subst h
    rw [zero_pow (show N + 1 ≠ 0 by omega), zero_add, one_pow] at hr'
    linarith

theorem strict_mono_aux (N : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    a ^ (N + 1) * (b + 1) ^ N < b ^ (N + 1) * (a + 1) ^ N := by
  have hb : 0 < b := by linarith
  have h1 : a * (b + 1) ≤ b * (a + 1) := by nlinarith
  have h2 : (a * (b + 1)) ^ N ≤ (b * (a + 1)) ^ N := pow_le_pow_left₀ (by positivity) h1 N
  have h3 : 0 < (b * (a + 1)) ^ N := by positivity
  calc a ^ (N + 1) * (b + 1) ^ N = a * (a * (b + 1)) ^ N := by rw [mul_pow]; ring
    _ ≤ a * (b * (a + 1)) ^ N := mul_le_mul_of_nonneg_left h2 ha.le
    _ < b * (b * (a + 1)) ^ N := mul_lt_mul_of_pos_right hab h3
    _ = b ^ (N + 1) * (a + 1) ^ N := by rw [mul_pow]; ring

theorem root_unique (N : ℕ) (ρ : ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hra : ρ * (a + 1) ^ N = a ^ (N + 1)) (hrb : ρ * (b + 1) ^ N = b ^ (N + 1)) : a = b := by
  have key : a ^ (N + 1) * (b + 1) ^ N = b ^ (N + 1) * (a + 1) ^ N := by
    rw [← hra, ← hrb]; ring
  rcases lt_trichotomy a b with h | h | h
  · have := strict_mono_aux N a b ha h; linarith
  · exact h
  · have := strict_mono_aux N b a hb h; linarith

theorem genGolden_eq (N : ℕ) (ρ r : ℝ) (hr : 0 < r) (hroot : ρ * (r + 1) ^ N = r ^ (N + 1)) :
    genGolden N ρ = r := by
  unfold genGolden
  have hset : {x : ℝ | 0 < x ∧ ρ * (x + 1) ^ N = x ^ (N + 1)} = {r} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxr⟩
      exact root_unique N ρ x r hx hr hxr hroot
    · rintro rfl
      exact ⟨hr, hroot⟩
  rw [hset, csSup_singleton]


/-- A feasible smoothness pair attaining `Φ^(d+1)`. -/
theorem feasible (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    ∃ l m : ℝ, 0 ≤ l ∧ 0 < m ∧ m * ρ < 1 ∧
      (∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → ∀ f : Polynomial ℝ,
        (f.natDegree ≤ d ∧ ∀ j, 0 ≤ f.coeff j) →
        y * f.eval (z + x + y) ≤ l * y * f.eval (z + y) + m * x * f.eval (z + x)) ∧
      genGolden d ρ ^ (d + 1) = l * ρ / (1 - m * ρ) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨r, hr0, hroot⟩ := root_exists (n + 1) ρ hρ0
  rw [genGolden_eq (n + 1) ρ r hr0 hroot]
  have hP : 0 < r + 1 := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (r + 1) ^ n * ((r + 1) + ((n : ℝ) + 1)) / ((n : ℝ) + 2) :=
    ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((n : ℝ) + 1) * (r + 1) ^ n / (((n : ℝ) + 2) * r ^ (n + 1)) :=
    ⟨_, rfl⟩
  have hl0 : 0 ≤ l := by rw [hl]; positivity
  have hm0 : 0 < m := by rw [hm]; positivity
  have hsum : l + m * r ^ (n + 1 + 1) = (r + 1) ^ (n + 1) := by
    have hr' : r ≠ 0 := hr0.ne'
    have hn2' : (n : ℝ) + 2 ≠ 0 := hn2.ne'
    rw [hl, hm]
    field_simp
    try ring
  have hρ' : ρ = r ^ (n + 1 + 1) / (r + 1) ^ (n + 1) := by
    rw [eq_div_iff (show (r + 1) ^ (n + 1) ≠ 0 by positivity)]
    exact hroot
  have hmρ : m * ρ = ((n : ℝ) + 1) * r / (((n : ℝ) + 2) * (r + 1)) := by
    have hr' : r ≠ 0 := hr0.ne'
    have hn2' : (n : ℝ) + 2 ≠ 0 := hn2.ne'
    have hP' : r + 1 ≠ 0 := hP.ne'
    rw [hm, hρ']
    field_simp
    try ring
  have hmρ1 : m * ρ < 1 := by
    rw [hmρ, div_lt_one (show (0:ℝ) < ((n : ℝ) + 2) * (r + 1) by positivity)]
    nlinarith
  refine ⟨l, m, hl0, hm0, hmρ1, ?_, ?_⟩
  · intro x y z hx hy hz f hf
    have D : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        y * (x + y) ^ (n + 1) ≤ l * (y * y ^ (n + 1)) + m * (x * x ^ (n + 1)) := by
      intro x y hx hy
      rw [hl, hm]
      exact degD n r hr0 x y hx hy
    exact polyL (n + 1) l m hl0 hm0.le D x y z hx hy hz f hf
  · have hne : 1 - m * ρ ≠ 0 := by linarith
    rw [eq_div_iff hne]
    linear_combination (-ρ) * hsum - hroot

noncomputable def gl {n r : ℕ} (G : Game n r) (s : G.Profile) (R : Finset (Fin n)) (e : Fin r) : ℝ :=
  ∑ u ∈ R, if e ∈ (s u).val then (G.demand u : ℝ) else 0

theorem load_eq {n r : ℕ} (G : Game n r) (s : G.Profile) (e : Fin r) :
    ((load G s e : ℝ≥0) : ℝ) = gl G s Finset.univ e := by
  unfold load gl
  rw [NNReal.coe_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp

theorem gl_split {n r : ℕ} (G : Game n r) (s : G.Profile) (R : Finset (Fin n)) (e : Fin r) :
    gl G s Finset.univ e = gl G s Rᶜ e + gl G s R e := by
  unfold gl
  rw [← Finset.sum_add_sum_compl R]
  ring

theorem gl_nonneg {n r : ℕ} (G : Game n r) (s : G.Profile) (R : Finset (Fin n)) (e : Fin r) :
    0 ≤ gl G s R e := by
  unfold gl
  refine Finset.sum_nonneg (fun u _ => ?_)
  split_ifs
  · exact NNReal.coe_nonneg _
  · exact le_rfl

theorem eval_mono (P : Polynomial ℝ) (hP : ∀ j, 0 ≤ P.coeff j) (a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) : P.eval a ≤ P.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab i) (hP i)

theorem swap {n r : ℕ} (G : Game n r) (t : G.Profile) (R : Finset (Fin n)) (F : Fin r → ℝ) :
    ∑ u ∈ R, ∑ e ∈ (t u).val, (G.demand u : ℝ) * F e = ∑ e : Fin r, gl G t R e * F e := by
  unfold gl
  simp_rw [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem_eq]

theorem gl_update_le {n r : ℕ} (G : Game n r) (s : G.Profile) (u : Fin n) (t : G.Strategy u)
    (e : Fin r) (he : e ∈ t.val) :
    gl G (Function.update s u t) Finset.univ e ≤ gl G s Finset.univ e + G.demand u := by
  unfold gl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u), ← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
  have hS : ∑ v ∈ Finset.univ.erase u,
      (if e ∈ (Function.update s u t v).val then (G.demand v : ℝ) else 0) =
      ∑ v ∈ Finset.univ.erase u, (if e ∈ (s v).val then (G.demand v : ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
  rw [hS, Function.update_self, if_pos he]
  have h0 : 0 ≤ (if e ∈ (s u).val then (G.demand u : ℝ) else 0) := by
    split_ifs
    · exact NNReal.coe_nonneg _
    · exact le_rfl
  linarith

theorem demand_le_gl {n r : ℕ} (G : Game n r) (t : G.Profile) (R : Finset (Fin n)) (u : Fin n)
    (hu : u ∈ R) (e : Fin r) (he : e ∈ (t u).val) : (G.demand u : ℝ) ≤ gl G t R e := by
  unfold gl
  have hle := Finset.single_le_sum (f := fun v => if e ∈ (t v).val then (G.demand v : ℝ) else 0)
    (fun v _ => by
      show 0 ≤ (if e ∈ (t v).val then (G.demand v : ℝ) else 0)
      split_ifs
      · exact NNReal.coe_nonneg _
      · exact le_rfl) hu
  simp only [he, ↓reduceIte] at hle
  exact hle

theorem groupCost_eq {n r : ℕ} (G : Game n r) (P : Fin r → Polynomial ℝ)
    (hcost : ∀ e (x : ℝ≥0), G.cost e x = (P e).eval (x : ℝ)) (R : Finset (Fin n)) (t : G.Profile) :
    gcost G R t = ∑ e : Fin r, gl G t R e * (P e).eval (gl G t Rᶜ e + gl G t R e) := by
  unfold gcost privateCost
  refine (swap G t R (fun e => G.cost e (load G t e))).trans ?_
  refine Finset.sum_congr rfl (fun e _ => ?_)
  show gl G t R e * G.cost e (load G t e) = _
  rw [hcost e, load_eq, gl_split G t R e]

theorem mainL {n r : ℕ} (G : Game n r) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (hG : CongestionApproxPNE.IsPolyGame d G) (R : Finset (Fin n)) (s sStar : G.Profile)
    (hs : IsGroupEq G ρ R s) (hout : ∀ u ∉ R, s u = sStar u) :
    gcost G R s ≤ genGolden d ρ ^ (d + 1) * gcost G R sStar := by
  choose P hdeg hcoef hcost using hG
  obtain ⟨l, m, hl0, hm0, hmρ, hsm, hΦ⟩ := feasible d ρ hd hρ
  have hρ0 : 0 < ρ := by linarith
  have hz : ∀ e, gl G sStar Rᶜ e = gl G s Rᶜ e := by
    intro e
    unfold gl
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [hout v (Finset.mem_compl.mp hv)]
  have hCs := groupCost_eq G P hcost R s
  have hCst := groupCost_eq G P hcost R sStar
  simp only [hz] at hCst
  -- equilibrium step
  have heq : gcost G R s ≤ ρ * ∑ e : Fin r, gl G sStar R e *
      (P e).eval (gl G s Rᶜ e + gl G s R e + gl G sStar R e) := by
    have h1 : ∀ u ∈ R, privateCost G s u ≤ ρ * ∑ e ∈ (sStar u).val, (G.demand u : ℝ) *
        (P e).eval (gl G s Rᶜ e + gl G s R e + gl G sStar R e) := by
      intro u hu
      refine le_trans (hs u hu (sStar u)) ?_
      refine mul_le_mul_of_nonneg_left ?_ hρ0.le
      unfold privateCost
      rw [Function.update_self]
      refine Finset.sum_le_sum (fun e he => ?_)
      rw [hcost e, load_eq]
      refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
      refine eval_mono (P e) (hcoef e) _ _ (gl_nonneg G _ _ e) ?_
      have a1 := gl_update_le G s u (sStar u) e he
      have a2 := demand_le_gl G sStar R u hu e he
      rw [gl_split G s R e] at a1
      linarith
    unfold gcost
    calc ∑ u ∈ R, privateCost G s u
        ≤ ∑ u ∈ R, ρ * ∑ e ∈ (sStar u).val, (G.demand u : ℝ) *
            (P e).eval (gl G s Rᶜ e + gl G s R e + gl G sStar R e) := Finset.sum_le_sum h1
      _ = ρ * ∑ e : Fin r, gl G sStar R e *
            (P e).eval (gl G s Rᶜ e + gl G s R e + gl G sStar R e) := by
          rw [← Finset.mul_sum]
          congr 1
          exact swap G sStar R _
  -- smoothness step
  have hsmooth : ∑ e : Fin r, gl G sStar R e *
      (P e).eval (gl G s Rᶜ e + gl G s R e + gl G sStar R e) ≤
      l * gcost G R sStar + m * gcost G R s := by
    rw [hCs, hCst, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun e _ => ?_)
    have := hsm (gl G s R e) (gl G sStar R e) (gl G s Rᶜ e) (gl_nonneg G _ _ e) (gl_nonneg G _ _ e)
      (gl_nonneg G _ _ e) (P e) ⟨hdeg e, hcoef e⟩
    linarith
  have hfin : gcost G R s ≤ ρ * (l * gcost G R sStar + m * gcost G R s) :=
    le_trans heq (mul_le_mul_of_nonneg_left hsmooth hρ0.le)
  rw [hΦ, div_mul_eq_mul_div, le_div_iff₀ (show (0:ℝ) < 1 - m * ρ by linarith)]
  linarith [hfin]

end Aux9b

open WeightedCongestionBR in
theorem solution {n r : ℕ} (G : Game n r) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u)
    (R : Finset (Fin n)) (s s' : G.Profile) (hs : IsGroupEq G ρ R s)
    (hout : ∀ u ∉ R, s u = s' u) :
    partialPot G R s ≤ alphaC d * genGolden d ρ ^ (d + 1) * partialPot G R s' := by
  have h5s := Aux9a.mainL G d hd hG hw R s
  have h5s' := Aux9a.mainL G d hd hG hw R s'
  have h1 := Aux9b.mainL G d ρ hd hρ hG R s s' hs hout
  have hα : 0 ≤ alphaC d := by unfold alphaC; positivity
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨r0, hr0, hroot⟩ := Aux9b.root_exists d ρ hρ0
  have hΦ : 0 ≤ genGolden d ρ ^ (d + 1) := by
    rw [Aux9b.genGolden_eq d ρ r0 hr0 hroot]
    positivity
  have step1 := h5s.2
  have step2 := mul_le_mul_of_nonneg_left h1 hα
  have step3 := mul_le_mul_of_nonneg_left h5s'.1 (mul_nonneg hα hΦ)
  calc partialPot G R s ≤ alphaC d * Aux9gc.gcost G R s := step1
    _ ≤ alphaC d * (genGolden d ρ ^ (d + 1) * Aux9gc.gcost G R s') := step2
    _ = alphaC d * genGolden d ρ ^ (d + 1) * Aux9gc.gcost G R s' := by ring
    _ ≤ alphaC d * genGolden d ρ ^ (d + 1) * partialPot G R s' := step3
