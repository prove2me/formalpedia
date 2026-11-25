-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.monF_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:40:57.360632+00:00
-- url     : https://prove2.me/submissions/7adb3705-34e0-477b-89ee-bdf4e8c07fa7

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
theorem _root_.solution (Cm : Matrix ι ι k) (α : ι → ZMod p) (l : ι) (x : ι → ZMod p) :
    monF Cm α x = lam Cm l x ^ (α l).val * ∏ j ∈ univ.erase l, lam Cm j x ^ (α j).val := by
  unfold monF
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ l)).symm
end ReciprocityTheory.PGsh.Up
