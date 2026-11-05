-- Prove2me | solution 1 for PaddedDescent.F.Mark.Size.sum_erase_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:03:47.836117+00:00
-- url     : https://prove2.me/submissions/5040b6d9-d25b-4d9c-bb3f-4a8f4c688a0c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}
namespace PaddedDescent.F.Mark.Size
theorem _root_.solution (a : Fin g) (F : ℕ → ℕ) : ∑ b ∈ (univ : Finset (Fin g)).erase a, F b.val = ∑ b ∈ (range g).erase a.val, F b := by
  refine sum_bij (fun b _ => b.val) ?_ ?_ ?_ ?_
  · intro b hb
    exact mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 (Fin.ext h), mem_range.2 b.2⟩
  · intro b _ b' _ h; exact Fin.ext h
  · intro b hb
    exact ⟨⟨b, mem_range.1 (mem_erase.1 hb).2⟩, mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 (congrArg Fin.val h), mem_univ _⟩, rfl⟩
  · intro b _; rfl
end PaddedDescent.F.Mark.Size
