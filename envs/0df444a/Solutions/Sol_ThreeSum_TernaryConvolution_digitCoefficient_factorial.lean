-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.digitCoefficient_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:46.576746+00:00
-- url     : https://prove2.me/submissions/b1b4692f-38e5-4c6f-be9c-e0637780e8fe

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
theorem _root_.solution (q a b : Fin 3) (h : a.val+b.val=q.val) :
    digitCoefficient q a b * (a.val.factorial : ℤ) * (b.val.factorial : ℤ) =
      (q.val.factorial : ℤ) := by
  fin_cases q <;> fin_cases a <;> fin_cases b <;>
    norm_num [digitCoefficient,inverseCoefficient,digitChoose,Fin.sum_univ_succ,
      Nat.choose,Nat.factorial,Fin.le_def] at *
end ThreeSum.TernaryConvolution
