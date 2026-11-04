-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.stages_zero_iff_convolution_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:18.970204+00:00
-- url     : https://prove2.me/submissions/85892cae-1f5b-483a-acaa-af433c8da13f

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_factorial_ne_zero
import Theorems.Thm_ThreeSum_TernaryConvolution_stages_factorial_convolution
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



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
        runZeta coords (fun B => factorial B*g B) R) Q=0 ↔
      convolution f g Q=0 := by
  rw [stages_factorial_convolution coords hn hall f g hf hg Q hQ]
  simp [factorial_ne_zero Q]
end ThreeSum.TernaryConvolution
