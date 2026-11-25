-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.prod_erase_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:38:10.735885+00:00
-- url     : https://prove2.me/submissions/1e7c5ef6-3cd0-4362-b3b6-5969f6e811a2

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] {ι : Type} [Fintype ι]
  [DecidableEq ι]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (Cm : Matrix ι ι k) (α : ι → ZMod p) (l : ι) (a : ZMod p)
    (x : ι → ZMod p) :
    ∏ j ∈ univ.erase l, lam Cm j x ^ (Function.update α l a j).val =
      ∏ j ∈ univ.erase l, lam Cm j x ^ (α j).val := by
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hj)]
end ReciprocityTheory.PGsh.Up
