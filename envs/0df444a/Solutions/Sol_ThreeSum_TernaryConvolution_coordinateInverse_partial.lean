-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.coordinateInverse_partial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:36.939402+00:00
-- url     : https://prove2.me/submissions/bb29fef4-8c6a-4d7d-aa1b-2d6662df482e

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_coordinateInverse_sum
import Theorems.Thm_ThreeSum_TernaryConvolution_coordinateInverse_kernel

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryConvolution
theorem _root_.solution {N : ℕ} (s : Finset (Fin N)) (i : Fin N)
    (hi : i∉s) (H : TritWord N → ℤ) :
    coordinateInverse i (partialInverse s H)=partialInverse (insert i s) H := by
  funext Q
  unfold partialInverse
  rw [coordinateInverse_sum]
  apply Finset.sum_congr rfl
  intro A hA
  exact coordinateInverse_kernel s i hi A Q (H A)
end ThreeSum.TernaryConvolution
