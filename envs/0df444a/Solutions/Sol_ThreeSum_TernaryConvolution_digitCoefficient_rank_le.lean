-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.digitCoefficient_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:39.02482+00:00
-- url     : https://prove2.me/submissions/9bba938e-3a42-433f-89bb-7743736117c3

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_digitCoefficient_zero_of_lt

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryConvolution
theorem _root_.solution (q a b : Fin 3) (h : digitCoefficient q a b≠0) :
    q.val≤a.val+b.val := by
  by_contra hn
  exact h (digitCoefficient_zero_of_lt q a b (by omega))
end ThreeSum.TernaryConvolution
