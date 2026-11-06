-- Prove2me | solution 1 for SplitCount.holds_petals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:56:59.797923+00:00
-- url     : https://prove2.me/submissions/a3c05f57-ff13-47a2-ba04-8904d0a8a55e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Disjoint

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight.Width
namespace SplitCount
theorem _root_.solution {b : ℕ → Bool} {s P : PFml} {H : PCl} (hP : ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q)
    (hH : ¬ ∃ l ∈ H, b l.1 = l.2) (hs : Holds b s) : Holds b P := by
  intro Q hQ
  obtain ⟨C, hC, hCQ⟩ := hP Q hQ
  obtain ⟨l, hl, hv⟩ := hs C hC
  rcases hCQ l hl with h | h
  · exact absurd ⟨l, h, hv⟩ hH
  · exact ⟨l, h, hv⟩
end SplitCount
