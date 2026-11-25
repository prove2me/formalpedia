-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.xc_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:54.931255+00:00
-- url     : https://prove2.me/submissions/545a4987-b33c-4835-8b4d-471a1941ac91

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
theorem _root_.solution (i : ι) (x : ι → ZMod p) : xc k i x ^ p = xc k i x := by
  simp only [xc, ← map_pow, ZMod.pow_card]
end ReciprocityTheory.PGsh.Up
