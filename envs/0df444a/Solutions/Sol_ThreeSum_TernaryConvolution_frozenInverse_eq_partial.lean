-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.frozenInverse_eq_partial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:37.011869+00:00
-- url     : https://prove2.me/submissions/e5bac434-a5a3-48b7-ad5d-81550994beb2

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_partialInverse_empty
import Theorems.Thm_ThreeSum_TernaryConvolution_coordinateInverse_partial
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryConvolution
theorem _root_.solution {N : ℕ} (coords : List (Fin N)) (h : coords.Nodup)
    (H : TritWord N → ℤ) : frozenInverse coords H=partialInverse coords.toFinset H := by
  induction coords with
  | nil => simpa [frozenInverse] using (partialInverse_empty H).symm
  | cons i rest ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp h
    change coordinateInverse i (frozenInverse rest H)=_
    rw [ih hn,List.toFinset_cons]
    exact coordinateInverse_partial rest.toFinset i (by simpa using hi) H
end ThreeSum.TernaryConvolution
