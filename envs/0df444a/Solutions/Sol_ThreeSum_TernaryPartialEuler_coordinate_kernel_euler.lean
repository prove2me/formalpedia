-- Prove2me | solution 1 for ThreeSum.TernaryPartialEuler.coordinate_kernel_euler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:31.571206+00:00
-- url     : https://prove2.me/submissions/8c322373-9ddf-4ea5-a8ed-f7499615fcbd

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Theorems.Thm_ThreeSum_TernaryPartialEuler_kernel_split
import Theorems.Thm_ThreeSum_TernaryPartialEuler_predecessor_kernel
import Theorems.Thm_ThreeSum_TernaryEuler_digit_euler


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryPartialEuler
theorem _root_.solution {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N)
    (i : Fin N) (hi : i∈S) :
    (R i).val*kernel S (predecessor R i) A=
      ((R i).val-(A i).val : ℤ)*kernel S R A := by
  rw [predecessor_kernel S R A i hi,kernel_split S R A i hi,←mul_assoc,digit_euler]
  ring
end ThreeSum.TernaryPartialEuler
