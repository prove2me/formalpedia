-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.monF_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:41:02.223159+00:00
-- url     : https://prove2.me/submissions/371f15f4-61d5-476f-b178-f79e4c96e747

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
theorem _root_.solution (Cm : Matrix ι ι k) : monF Cm (0 : ι → ZMod p) = 1 := by
  funext x
  simp [monF]
end ReciprocityTheory.PGsh.Up
