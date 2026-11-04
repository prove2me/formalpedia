-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.coefficient_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:47.715198+00:00
-- url     : https://prove2.me/submissions/67374a1f-7df7-4c4c-b43c-40b05fbde3c3

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryConvolution
theorem _root_.solution {N : ℕ} (Q A B : TritWord N) :
    (∑ R : TritWord N, inverseWeight Q R * weight R A * weight R B) =
      pairCoefficient Q A B := by
  unfold pairCoefficient digitCoefficient
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro R hR
  unfold inverseWeight weight
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
end ThreeSum.TernaryConvolution
