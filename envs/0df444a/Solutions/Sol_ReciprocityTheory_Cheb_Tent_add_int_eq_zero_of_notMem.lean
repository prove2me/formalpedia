-- Prove2me | solution 1 for ReciprocityTheory.Cheb.Tent_add_int_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:46.273523+00:00
-- url     : https://prove2.me/submissions/1c8766ad-6b7a-41d9-ae44-6a8419b02f4b

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
import Theorems.Thm_ReciprocityTheory_Cheb_tent_add_int_eq_zero_of_notMem__f19901

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
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.Cheb
theorem _root_.solution [DecidableEq ι] (y : ι → ℝ) {n : ι → ℤ}
    (hn : n ∉ Fintype.piFinset fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)) :
    Tent (fun i => y i + n i) = 0 := by
  rw [Fintype.mem_piFinset] at hn
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  exact prod_eq_zero (mem_univ i) (tent_add_int_eq_zero_of_notMem (y i) hi)
end ReciprocityTheory.Cheb
