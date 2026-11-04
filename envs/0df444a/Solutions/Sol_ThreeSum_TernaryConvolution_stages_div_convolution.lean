-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.stages_div_convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:17.925254+00:00
-- url     : https://prove2.me/submissions/fb10c415-114c-4327-84a6-1551862debf1

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_factorial_ne_zero
import Theorems.Thm_ThreeSum_TernaryConvolution_stages_factorial_convolution

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryConvolution
theorem _root_.solution {N a b : ℕ} (coords : List (Fin N))
    (hn : coords.Nodup) (hall : coords.toFinset=univ) (f g : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    runInverse coords
      (fun R => runZeta coords (fun A => factorial A*f A) R *
        runZeta coords (fun B => factorial B*g B) R) Q / factorial Q =
      convolution f g Q := by
  rw [stages_factorial_convolution coords hn hall f g hf hg Q hQ]
  exact Int.mul_ediv_cancel_left _ (factorial_ne_zero Q)
end ThreeSum.TernaryConvolution
