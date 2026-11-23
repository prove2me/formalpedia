-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.MulStable.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:57.618892+00:00
-- url     : https://prove2.me/submissions/9c89b64c-6ee0-4b37-af28-05ad13d51dbc

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
theorem _root_.solution {S : Submodule k ((ι → ZMod p) → k)} {h₁ h₂ : (ι → ZMod p) → k}
    (a : MulStable S h₁) (b : MulStable S h₂) : MulStable S (h₁ + h₂) := by
  intro f hf
  rw [add_mul]
  exact S.add_mem (a f hf) (b f hf)
end MulStable
end ReciprocityTheory.PGsh.Up
