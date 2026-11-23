-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.MulStable.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:31.991679+00:00
-- url     : https://prove2.me/submissions/039ea4a7-4fcb-4de6-a1e7-c72f01a95cd8

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
namespace MulStable
theorem _root_.solution (S : Submodule k ((ι → ZMod p) → k)) (c : k) :
    MulStable S (fun _ => c) := by
  intro f hf
  have e : (fun _ => c) * f = c • f := by funext x; simp
  rw [e]
  exact S.smul_mem c hf
end MulStable
end ReciprocityTheory.PGsh.Up
