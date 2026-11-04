-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPotentialBatch.receipt_final
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:42:04.996243+00:00
-- url     : https://prove2.me/submissions/09f87d77-e4a6-4838-b599-3f42e87c29e9

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatch
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatchFinal
import Theorems.Thm_ThreeSum_LightTernaryPairedPotentialBatch_total_eq_of_reads
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPairedPotentialBatch
open Light
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPotentialBatch
theorem _root_.solution {lim : Limits} {P : Program} {p d t K base Λ H cutoff : ℕ}
    {argv : List ℤ} {μ : ℕ→ℤ} (hΛ : 1≤Λ) (hend : base+H*Λ^4≤cutoff)
    (h : Meets lim P p d argv μ t
      (fun r ν => r=total K base Λ μ H ∧ Kept μ ν cutoff)) :
    Meets lim P p d argv μ t (fun r ν => r=total K base Λ ν H ∧ Kept μ ν cutoff) := by
  apply h.mono le_rfl
  rintro r ν ⟨hr,hkeep⟩
  refine ⟨hr.trans (total_eq_of_reads K base Λ H μ ν hΛ ?_),hkeep⟩
  intro i hi q hq
  apply Eq.symm
  apply hkeep
  have hh := Nat.mul_le_mul_right (Λ^4) (by omega : i+1≤H)
  nlinarith
end ThreeSum.LightTernaryPairedPotentialBatch
