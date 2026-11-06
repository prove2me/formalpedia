-- Prove2me | solution 1 for SplitCount.round_iterate_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:31:53.90884+00:00
-- url     : https://prove2.me/submissions/cc59dd99-bebf-4f54-bbb9-eaafd69b84c2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Tree
import Theorems.Thm_SplitCount_round_map
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight Eight.Width
variable {σ ρ : Type} {s₁ : σ → Option (σ × σ)} {s₂ : ρ → Option (ρ × ρ)} {f : σ → ρ}
namespace SplitCount
theorem _root_.solution (h : ∀ x, s₂ (f x) = (s₁ x).map fun lh => (f lh.1, f lh.2)) (i : ℕ) (p : List σ × List σ) :
    (round s₂)^[i] (p.1.map f, p.2.map f) = (((round s₁)^[i] p).1.map f, ((round s₁)^[i] p).2.map f) := by
  induction i generalizing p with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, round_map h, ih]
end SplitCount
