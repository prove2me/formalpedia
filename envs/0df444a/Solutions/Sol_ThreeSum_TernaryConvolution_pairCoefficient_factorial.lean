-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.pairCoefficient_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:15.482209+00:00
-- url     : https://prove2.me/submissions/15f3bb6e-0da0-4bf7-9045-8e41c9ce5c81

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_digitCoefficient_factorial
import Theorems.Thm_ThreeSum_TernaryConvolution_pairCoefficient_adds
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
theorem _root_.solution {N : ℕ} (Q A B : TritWord N)
    (hrank : rank A+rank B=rank Q) :
    pairCoefficient Q A B * factorial A * factorial B =
      if Adds A B Q then factorial Q else 0 := by
  by_cases hadd : Adds A B Q
  · simp only [hadd,↓reduceIte]
    unfold pairCoefficient factorial
    rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact digitCoefficient_factorial _ _ _ (hadd i)
  · have hz : pairCoefficient Q A B=0 := by
      by_contra hn
      exact hadd (pairCoefficient_adds Q A B hrank hn)
    simp [hadd,hz]
end ThreeSum.TernaryConvolution
