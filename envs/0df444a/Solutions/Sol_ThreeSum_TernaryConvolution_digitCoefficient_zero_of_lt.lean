-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.digitCoefficient_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:45.609921+00:00
-- url     : https://prove2.me/submissions/b0a7041c-750e-4e11-856d-9b1bdf0cfe8a

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
theorem _root_.solution (q a b : Fin 3)
    (h : a.val+b.val<q.val) : digitCoefficient q a b=0 := by
  fin_cases q <;> fin_cases a <;> fin_cases b <;>
    norm_num [digitCoefficient,inverseCoefficient,digitChoose,Fin.sum_univ_succ,
      Nat.choose,Fin.le_def] at *
end ThreeSum.TernaryConvolution
