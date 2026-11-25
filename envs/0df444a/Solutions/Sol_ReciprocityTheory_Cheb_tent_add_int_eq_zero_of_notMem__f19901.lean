-- Prove2me | solution 1 for ReciprocityTheory.Cheb.tent_add_int_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:38.155617+00:00
-- url     : https://prove2.me/submissions/831d4ebd-f3fc-4ccd-92b8-7a71bfcdf715

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
import Theorems.Thm_ReciprocityTheory_Cheb_tent_of_one_le_abs

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
theorem _root_.solution (t : ℝ) {n : ℤ} (hn : n ∉ ({-⌊t⌋, -⌊t⌋ - 1} : Finset ℤ)) :
    tent (t + n) = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  apply tent_of_one_le_abs
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  rcases lt_or_gt_of_ne hn.1 with h | h
  · have : n ≤ -⌊t⌋ - 2 := by omega
    have : (n : ℝ) ≤ -⌊t⌋ - 2 := by exact_mod_cast this
    rw [abs_of_neg (by linarith)]; linarith
  · have : (n : ℝ) ≥ -⌊t⌋ + 1 := by exact_mod_cast (show n ≥ -⌊t⌋ + 1 by omega)
    rw [abs_of_nonneg (by linarith)]; linarith
end ReciprocityTheory.Cheb
