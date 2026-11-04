-- Prove2me | solution 1 for ThreeSum.Reporting.mass_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:26.840236+00:00
-- url     : https://prove2.me/submissions/00f05402-8c7e-4496-9497-9718f3133ff3

import Definitions.Def_Submission_ThreeSum_Subset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Definitions.Def_Submission_ThreeSum_Reporting

set_option autoImplicit false
open ThreeSum ThreeSum.Reporting
open Finset
open scoped BigOperators
variable {ι α : Type*} [DecidableEq α]
namespace ThreeSum.Reporting
theorem _root_.solution (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (k : ℕ) (pre : List α) :
    0 < mass I word weight k pre ↔
      ∃ i ∈ I, (word i).take k = pre ∧ 0 < weight i := by
  unfold mass Subset.fiberMass
  rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [mem_filter]
  constructor
  · rintro ⟨i, ⟨hi, hpre⟩, hw⟩
    exact ⟨i, hi, hpre, hw⟩
  · rintro ⟨i, hi, hpre, hw⟩
    exact ⟨i, ⟨hi, hpre⟩, hw⟩
end ThreeSum.Reporting
