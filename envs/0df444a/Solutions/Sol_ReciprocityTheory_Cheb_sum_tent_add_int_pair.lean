-- Prove2me | solution 1 for ReciprocityTheory.Cheb.sum_tent_add_int_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:57:46.274004+00:00
-- url     : https://prove2.me/submissions/45a837eb-27d0-4f6b-9421-af313e298a86

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
import Theorems.Thm_ReciprocityTheory_Cheb_tent_of_abs_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (t : ℝ) :
    ∑ n ∈ ({-⌊t⌋, -⌊t⌋ - 1} : Finset ℤ), tent (t + n) = 1 := by
  have hne : (-⌊t⌋ : ℤ) ≠ -⌊t⌋ - 1 := by omega
  rw [Finset.sum_pair hne]
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  push_cast
  rw [tent_of_abs_le, tent_of_abs_le]
  · rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)]; ring
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
end ReciprocityTheory.Cheb
