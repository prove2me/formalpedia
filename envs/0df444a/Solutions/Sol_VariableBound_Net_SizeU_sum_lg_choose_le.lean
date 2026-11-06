-- Prove2me | solution 1 for VariableBound.Net.SizeU.sum_lg_choose_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:59:05.226543+00:00
-- url     : https://prove2.me/submissions/b072196b-e121-42c4-b4f7-6d79cf196279

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeU
import Theorems.Thm_ClauseBound_ParityChecks_prod_choose_le


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}
namespace VariableBound.Net.SizeU
theorem _root_.solution (g : ℕ) (t μ : ℕ → ℕ → ℕ) (h : ∀ b < g, ∀ a < b, μ a b ≤ t a b) :
    ∑ b ∈ range g, ∑ a ∈ range b, lg ((t a b).choose (μ a b)) ≤
      lg ((∑ b ∈ range g, ∑ a ∈ range b, t a b).choose (∑ b ∈ range g, ∑ a ∈ range b, μ a b)) := by
  have hpos : ∀ x ∈ (range g).sigma fun b => range b, 1 ≤ (t x.2 x.1).choose (μ x.2 x.1) := fun x hx =>
    Nat.choose_pos (h x.1 (mem_range.1 (mem_sigma.1 hx).1) x.2 (mem_range.1 (mem_sigma.1 hx).2))
  rw [sum_sigma' (range g) (fun b => range b) fun b a => lg ((t a b).choose (μ a b)),
    sum_sigma' (range g) (fun b => range b) fun b a => t a b, sum_sigma' (range g) (fun b => range b) fun b a => μ a b]
  unfold lg
  rw [← Real.logb_prod _ _ fun x hx => by exact_mod_cast (Nat.pos_iff_ne_zero.1 (hpos x hx))]
  refine Real.logb_le_logb_of_le (by norm_num) (prod_pos fun x hx => by exact_mod_cast hpos x hx) ?_
  exact_mod_cast ClauseBound.ParityChecks.prod_choose_le ((range g).sigma fun b => range b) (fun x => t x.2 x.1) fun x => μ x.2 x.1
end VariableBound.Net.SizeU
