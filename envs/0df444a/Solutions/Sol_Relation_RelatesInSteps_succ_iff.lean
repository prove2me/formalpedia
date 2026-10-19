-- Prove2me | solution 1 for Relation.RelatesInSteps.succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:38:49.580694+00:00
-- url     : https://prove2.me/submissions/40614813-c827-4570-a4fa-fcb5da67c3ad

/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

/-
Vendored from CSLib (https://github.com/leanprover/cslib), upstream file
  Cslib/Foundations/Data/RelatesInSteps.lean
at commit 3aa9d4416c185e0b9faeb72bbd65abe85b95dbcc (2026-08-03); fetched 2026-08-05.

CSLib cannot currently be a Lake dependency of this project: its MultiTape development
requires Lean >= v4.33.0-rc1, while this project pins v4.32.0. See
`planning/tm-infrastructure.md` (decision D1). Delete this copy and `require` CSLib once
the toolchains align.

Adaptations (the only differences from upstream):
* module-system markers removed: the `module` line, `public import` -> `import`, and the
  `@[expose] public section` line (replaced by the `set_option` lines below);
* `set_option autoImplicit true` / `set_option relaxedAutoImplicit true` added to restore
  the upstream Lean defaults (this project's lakefile disables both);
* `import Cslib.Init` dropped (only needed under the module system); in its stead,
  `import Mathlib.Data.Nat.Notation` added — upstream receives the `ℕ` notation through
  `Cslib.Init`, and `Mathlib.Logic.Relation` alone does not provide it.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Cslib/Foundations/Data/RelatesInSteps.lean (solution of Relation.RelatesInSteps.succ_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace Relation
section
set_option autoImplicit true
set_option relaxedAutoImplicit true
variable {α : Type*} {r : α → α → Prop} {a b c : α}
lemma RelatesInSteps.succ {n : ℕ} (h : RelatesInSteps r a b (n + 1)) :
    ∃ t', RelatesInSteps r a t' n ∧ r t' b := by
  cases h with
  | tail t' _ _ hsteps hstep => exact ⟨t', hsteps, hstep⟩
end
end Relation

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace Relation.RelatesInSteps
set_option autoImplicit true
set_option relaxedAutoImplicit true
variable {α : Type*} {r : α → α → Prop} {a b c : α}
theorem _root_.solution {a b : α} {n : ℕ} :
    RelatesInSteps r a b (n + 1) ↔ ∃ t', RelatesInSteps r a t' n ∧ r t' b := by
  constructor
  · exact RelatesInSteps.succ
  · rintro ⟨t', h_steps, h_red⟩
    exact .tail _ t' b n h_steps h_red
end Relation.RelatesInSteps
