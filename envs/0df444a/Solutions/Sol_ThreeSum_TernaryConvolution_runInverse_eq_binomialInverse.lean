-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.runInverse_eq_binomialInverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:18.810716+00:00
-- url     : https://prove2.me/submissions/deb94eb8-3b05-412e-9bda-23fb6f78c330

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_frozenInverse_eq_binomialInverse
import Theorems.Thm_ThreeSum_TernaryConvolution_runInverse_eq_frozen_reverse
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
theorem _root_.solution {N : ℕ} (coords : List (Fin N))
    (h : coords.Nodup) (hall : coords.toFinset=univ) (H : TritWord N → ℤ) :
    runInverse coords H=binomialInverse H := by
  rw [runInverse_eq_frozen_reverse]
  exact frozenInverse_eq_binomialInverse coords.reverse (by simpa using h)
    (by simpa using hall) H
end ThreeSum.TernaryConvolution
