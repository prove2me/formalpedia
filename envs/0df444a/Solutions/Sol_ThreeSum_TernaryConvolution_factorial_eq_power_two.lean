-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.factorial_eq_power_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:38.765854+00:00
-- url     : https://prove2.me/submissions/f129453e-a81f-4efa-af28-2691bbd40a3f

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
theorem _root_.solution {N : ℕ} (A : TritWord N) :
    factorial A=(2 : ℤ)^digitCount A 2 := by
  have hlocal (d : Fin 3) : (d.val.factorial : ℤ) =
      (2 : ℤ)^(if d=2 then 1 else 0 : ℕ) := by
    fin_cases d <;> norm_num [Fin.ext_iff,Nat.factorial]
  unfold factorial
  simp_rw [hlocal]
  rw [Finset.prod_pow_eq_pow_sum]
  rfl
end ThreeSum.TernaryConvolution
