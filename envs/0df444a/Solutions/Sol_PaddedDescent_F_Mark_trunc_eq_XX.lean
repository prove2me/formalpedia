-- Prove2me | solution 1 for PaddedDescent.F.Mark.trunc_eq_XX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:04:27.835379+00:00
-- url     : https://prove2.me/submissions/cf4fc0e9-773a-4c58-b6c2-66630b926080

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_PaddedDescent_F_MarkLayers
import Theorems.Thm_PaddedDescent_F_Mark_trunc_of_good


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers
namespace PaddedDescent.F.Mark
theorem _root_.solution {n w : ℕ} {Λ : Fml} {rest : List Fml} (h : Good n w (Λ :: rest)) : trunc n w (Λ :: rest) = (XX n Λ rest : ℤ) := by
  rw [trunc_of_good h, XX, Nat.cast_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hs : satL (ext σ) rest
  · rw [if_pos hs, if_pos (show ∀ L ∈ rest, nvio (ext σ) L = 0 from hs)]; norm_cast
  · rw [if_neg hs, if_neg (show ¬ ∀ L ∈ rest, nvio (ext σ) L = 0 from hs)]; norm_cast
end PaddedDescent.F.Mark
