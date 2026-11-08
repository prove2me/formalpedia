-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P45.effectiveLink
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:02:04.545868+00:00
-- url     : https://prove2.me/submissions/7adffd0f-c8de-445b-8247-34117b667f42

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P45

open scoped BigOperators

noncomputable section

open QAlgorithms.Papers.Independent.Intakethird100.P45 in
theorem solution (S : ℕ) (hS : 0 < S) (p0 : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : p0 ≤ 1) :
    retainedLinkProbability S p0 = 1 - (1 - p0) ^ S := by
  suffices hmain : (∑ flags : Fin S → Bool,
      if ∃ i, flags i = true then iidMass p0 flags else 0) = 1 - (1 - p0) ^ S by
    unfold retainedLinkProbability bernoulliFlagEvent
    convert hmain
  have htot : ∑ flags : Fin S → Bool, iidMass p0 flags = 1 := by
    unfold iidMass
    have h := Fintype.prod_sum (fun (_ : Fin S) (b : Bool) => if b then p0 else 1 - p0)
    simp only [Fintype.sum_bool] at h
    norm_num at h
    exact h.symm
  have hc : ∑ flags : Fin S → Bool,
      (if flags = (fun _ => false) then iidMass p0 flags else 0) = (1 - p0) ^ S := by
    rw [Finset.sum_ite_eq' Finset.univ (fun _ => false) (fun f => iidMass p0 f),
      if_pos (Finset.mem_univ _)]
    unfold iidMass
    simp
  rw [← hc, ← htot, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro flags _
  by_cases h : ∃ i, flags i = true
  · have hne : flags ≠ (fun _ => false) := by
      rintro rfl
      obtain ⟨i, hi⟩ := h
      exact Bool.false_ne_true hi
    rw [if_pos h, if_neg hne, sub_zero]
  · have heq : flags = (fun _ => false) := by
      funext i
      push_neg at h
      simpa using h i
    rw [if_neg h, if_pos heq, sub_self]

end
