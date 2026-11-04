-- Prove2me | solution 1 for ThreeSum.BlockSourceEncoding.count_eq_sum_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:06:40.888689+00:00
-- url     : https://prove2.me/submissions/06345dbd-a03f-4eb5-9542-c835cf81dbe3

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
import Theorems.Thm_ThreeSum_BlockSourceEncoding_count_eq_sum

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceEncoding
open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace ThreeSum.BlockSourceEncoding
theorem _root_.solution {β : Type*} [DecidableEq β]
    {p m n : ℕ} (hm : 0 < m) (shift endpoint : ℤ)
    (B : Finset β) (b : β → ℤ) (values : ℕ → ℤ)
    (e : Fin n ≃ B) (hvalues : ∀ i : Fin n, values i.val = b (e i)) :
    LightHistogram.count (fun i => key p m shift (values i))
      (LightResidues.residue m 1 endpoint) n =
        ∑ i ∈ B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by
  rw [count_eq_sum hm,← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by
      apply Fintype.sum_equiv e
      intro i
      rw [hvalues i]
    _ = _ := Finset.sum_coe_sort B
      (fun i : β => if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then (1 : ℕ) else 0)
end ThreeSum.BlockSourceEncoding
