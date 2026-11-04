-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.stages_factorial_convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:41:11.59034+00:00
-- url     : https://prove2.me/submissions/fc09bdda-29b3-46de-8675-99f367f8d139

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_runInverse_eq_binomialInverse
import Theorems.Thm_ThreeSum_TernaryConvolution_factorial_convolution
import Theorems.Thm_ThreeSum_TernaryTransform_runZeta_eq_binomialZeta


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
        runZeta coords (fun B => factorial B*g B) R) Q =
      factorial Q * convolution f g Q := by
  rw [runInverse_eq_binomialInverse coords hn hall,
    ThreeSum.TernaryTransform.runZeta_eq_binomialZeta coords hn hall,
    ThreeSum.TernaryTransform.runZeta_eq_binomialZeta coords hn hall]
  exact factorial_convolution f g hf hg Q hQ
end ThreeSum.TernaryConvolution
