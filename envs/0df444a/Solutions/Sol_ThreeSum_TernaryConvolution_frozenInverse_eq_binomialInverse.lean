-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.frozenInverse_eq_binomialInverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:14.446201+00:00
-- url     : https://prove2.me/submissions/3b870b65-da21-41a5-9eab-86543f4d9680

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_partialInverse_univ
import Theorems.Thm_ThreeSum_TernaryConvolution_frozenInverse_eq_partial

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryConvolution
theorem _root_.solution {N : ℕ} (coords : List (Fin N))
    (h : coords.Nodup) (hall : coords.toFinset=univ) (H : TritWord N → ℤ) :
    frozenInverse coords H=binomialInverse H := by
  rw [frozenInverse_eq_partial coords h,hall,partialInverse_univ]
end ThreeSum.TernaryConvolution
