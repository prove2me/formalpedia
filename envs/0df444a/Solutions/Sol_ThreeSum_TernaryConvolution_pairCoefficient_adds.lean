-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.pairCoefficient_adds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:38.245195+00:00
-- url     : https://prove2.me/submissions/1071db5c-d02c-48ba-bf8d-e3ea71c43b78

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_digitCoefficient_rank_le

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryConvolution
theorem _root_.solution {N : ℕ} (Q A B : TritWord N)
    (hrank : rank A+rank B=rank Q) (hn : pairCoefficient Q A B≠0) : Adds A B Q := by
  have hlocal : ∀ i, digitCoefficient (Q i) (A i) (B i)≠0 := by
    intro i hz
    apply hn
    unfold pairCoefficient
    exact Finset.prod_eq_zero (mem_univ i) hz
  have hle : ∀ i, (Q i).val≤(A i).val+(B i).val :=
    fun i => digitCoefficient_rank_le _ _ _ (hlocal i)
  intro i
  by_contra hn
  have hlei := hle i
  have hlt : (Q i).val<(A i).val+(B i).val := by omega
  have hs := Finset.sum_lt_sum (fun j (_ : j ∈ (univ : Finset (Fin N))) => hle j)
    ⟨i,mem_univ i,hlt⟩
  rw [Finset.sum_add_distrib] at hs
  change rank Q<rank A+rank B at hs
  omega
end ThreeSum.TernaryConvolution
