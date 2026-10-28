-- Prove2me | solution 1 for UniformDRO.Concentration.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:27:30.03972+00:00
-- url     : https://prove2.me/submissions/aeeae21b-83cf-4251-bcd0-33c3cac503aa

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_conj
import Definitions.Def_UniformDRO_Concentration_RobustRisk

namespace Aux_UniformDRO_Concentration_lemma_3

open UniformDRO.Concentration

lemma alg (k s t T M : ℝ) (hk : 1 < k) :
    s * t - cressieRead k t = (k * ((k - 1) * s + 1) * t - T - (k - 1)) / (k * (k - 1)) +
      (T - t ^ k) / (k * (k - 1)) ∧
    1 / k * M - 1 / k = ((k - 1) * M - (k - 1)) / (k * (k - 1)) := by
  have h1 : k - 1 ≠ 0 := by linarith
  have h2 : k ≠ 0 := by linarith
  unfold cressieRead
  constructor
  · field_simp
    ring
  · field_simp

lemma upper (k s t : ℝ) (hk : 1 < k) (ht : 0 ≤ t) :
    s * t - cressieRead k t ≤ 1 / k * (max ((k - 1) * s + 1) 0) ^ kstar k - 1 / k := by
  set u := (k - 1) * s + 1 with hu
  have hkk : 0 < k * (k - 1) := by nlinarith
  have key : k * u * t - t ^ k ≤ (k - 1) * (max u 0) ^ kstar k := by
    rcases le_or_gt u 0 with h | h
    · rw [max_eq_right h, Real.zero_rpow (by unfold kstar; positivity)]
      have : 0 ≤ t ^ k := Real.rpow_nonneg ht k
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ k) ht]
    · rw [max_eq_left h.le]
      have hc : (kstar k).HolderConjugate k := (Real.HolderConjugate.conjExponent hk).symm
      have hy := Real.young_inequality_of_nonneg h.le ht hc
      have hks : kstar k = k / (k - 1) := rfl
      have hk1 : k - 1 ≠ 0 := by linarith
      have : k * (u ^ kstar k / kstar k) = (k - 1) * u ^ kstar k := by
        rw [hks]; field_simp
      have h3 : k * (t ^ k / k) = t ^ k := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hy (by linarith : (0:ℝ) ≤ k)]
  obtain ⟨e1, e2⟩ := alg k s t (t ^ k) ((max u 0) ^ kstar k) hk
  rw [e1, e2, sub_self, zero_div, add_zero]
  apply div_le_div_of_nonneg_right _ hkk.le
  linarith

lemma attain (k s : ℝ) (hk : 1 < k) :
    ∃ t, 0 ≤ t ∧ s * t - cressieRead k t =
      1 / k * (max ((k - 1) * s + 1) 0) ^ kstar k - 1 / k := by
  set u := (k - 1) * s + 1 with hu
  have hk0 : k ≠ 0 := by linarith
  have hk1 : k - 1 ≠ 0 := by linarith
  rcases le_or_gt u 0 with h | h
  · refine ⟨0, le_rfl, ?_⟩
    rw [max_eq_right h, Real.zero_rpow (by unfold kstar; positivity)]
    unfold cressieRead
    rw [Real.zero_rpow hk0]
    field_simp
    ring
  · refine ⟨u ^ (1 / (k - 1)), Real.rpow_nonneg h.le _, ?_⟩
    rw [max_eq_left h.le]
    obtain ⟨e1, e2⟩ := alg k s (u ^ (1 / (k - 1))) ((u ^ (1 / (k - 1))) ^ k)
      (u ^ kstar k) hk
    rw [e1, e2, sub_self, zero_div, add_zero]
    have hp1 : (u ^ (1 / (k - 1))) ^ k = u ^ kstar k := by
      rw [← Real.rpow_mul h.le]
      congr 1
      unfold kstar
      field_simp
    have hp2 : u * u ^ (1 / (k - 1)) = u ^ kstar k := by
      calc u * u ^ (1 / (k - 1)) = u ^ (1 : ℝ) * u ^ (1 / (k - 1)) := by rw [Real.rpow_one]
        _ = u ^ ((1 : ℝ) + 1 / (k - 1)) := (Real.rpow_add h _ _).symm
        _ = u ^ kstar k := by
          congr 1
          unfold kstar
          field_simp
          ring
    rw [← hu] at e1
    rw [hp1, mul_assoc, hp2]
    congr 1
    ring

end Aux_UniformDRO_Concentration_lemma_3

open Aux_UniformDRO_Concentration_lemma_3 in
open UniformDRO.Concentration in
theorem solution (k : ℝ) (hk : 1 < k) (s : ℝ) :
    PhiDivRobust.Counterpart.conj (fun t => ((cressieRead k t : ℝ) : EReal)) s =
      ((1 / k * (max ((k - 1) * s + 1) 0) ^ kstar k - 1 / k : ℝ) : EReal) := by
  unfold PhiDivRobust.Counterpart.conj
  simp only [← EReal.coe_sub]
  apply le_antisymm
  · apply iSup₂_le
    intro t ht
    exact EReal.coe_le_coe_iff.2 (upper k s t hk ht)
  · obtain ⟨t, ht, heq⟩ := attain k s hk
    rw [← heq]
    exact le_iSup₂_of_le (f := fun t (_ : t ∈ Set.Ici (0 : ℝ)) =>
      ((s * t - cressieRead k t : ℝ) : EReal)) t ht le_rfl
