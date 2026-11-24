-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.MulStable.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:21.375958+00:00
-- url     : https://prove2.me/submissions/871659e4-6693-407a-8fac-51926ab24de8

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_mul

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
theorem _root_.solution {S : Submodule k ((ι → ZMod p) → k)} {h : (ι → ZMod p) → k}
    (a : MulStable S h) (n : ℕ) : MulStable S (h ^ n) := by
  induction n with
  | zero => intro f hf; simpa using hf
  | succ n ih => rw [pow_succ]; exact ih.mul a
end MulStable
end ReciprocityTheory.PGsh.Up
