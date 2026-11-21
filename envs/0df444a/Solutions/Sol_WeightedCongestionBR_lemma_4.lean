-- Prove2me | solution 1 for WeightedCongestionBR.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:48:14.199217+00:00
-- url     : https://prove2.me/submissions/19978343-b2d6-47cd-abee-1dd9068d337b

import Mathlib
import Definitions.Def_WeightedCongestionBR_IsPd
import Definitions.Def_WeightedCongestionBR_phiPoly
import Definitions.Def_WeightedCongestionBR_alphaC
set_option autoImplicit false
open scoped NNReal

namespace Aux_WeightedCongestionBR_lemma_4

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

end Aux_WeightedCongestionBR_lemma_4

open WeightedCongestionBR Aux_WeightedCongestionBR_lemma_4 in
theorem solution (d : ℕ) (hd : 1 ≤ d) (P : Polynomial ℝ) (hP : IsPd d P) (x w : ℝ) (hx : 0 ≤ x)
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
