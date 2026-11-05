-- Prove2me | solution 1 for VariableBound.Net.Tests.sum_erase_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:27:38.095565+00:00
-- url     : https://prove2.me/submissions/b29f7f2b-dbb8-4b82-9d0f-082f15cec039

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}
namespace VariableBound.Net.Tests
theorem _root_.solution (a : Fin g) (F : ℕ → ℕ) : ∑ b ∈ (univ : Finset (Fin g)).erase a, F b.val = ∑ b ∈ (range g).erase a.val, F b := by
  refine sum_bij (fun b _ => b.val) ?_ ?_ ?_ ?_
  · intro b hb
    exact mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 (Fin.ext h), mem_range.2 b.2⟩
  · intro b _ b' _ h; exact Fin.ext h
  · intro b hb
    exact ⟨⟨b, mem_range.1 (mem_erase.1 hb).2⟩, mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 (congrArg Fin.val h), mem_univ _⟩, rfl⟩
  · intro b _; rfl
end VariableBound.Net.Tests
