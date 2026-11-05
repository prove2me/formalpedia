-- Prove2me | solution 1 for VariableBound.StepParity.cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:45:30.02249+00:00
-- url     : https://prove2.me/submissions/42d92fec-37ad-4edb-bc42-da00dd2d5720

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_StepParity
import Theorems.Thm_VariableBound_StepParity_allEven_eq_fin
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_cutoff_one


set_option autoImplicit false
section
section
open VariableBound VariableBound.StepParity
open Finset ParityChecks AppVariables
variable {X E : Type} [DecidableEq E]
variable [Fintype X]
namespace VariableBound.StepParity
theorem _root_.solution (V : X → Finset E) (L : List (Finset E)) (φ : X → ℤ) {ν M' : ℕ} (hν : 1 ≤ ν) (hM : ν - 1 + L.length ≤ M') :
    ∑ ξ, φ ξ * allEven V L ξ ≡ ∑ ξ, φ ξ * ∑ S ∈ tup V L M' ξ, ∏ j, sig #(S j) [ZMOD 2 ^ ν] := by
  refine Int.ModEq.sum fun ξ _ => Int.ModEq.mul_left _ ?_
  have h := ClauseBound.ParityChecks.StepOne.cutoff_one (M := M') (disjoint_empty_right (univ : Finset (Fin L.length))) (fun j => L.getD j ∅ ∩ V ξ) hν
    (by rw [card_univ, Fintype.card_fin]; exact hM)
  simp only [prod_empty, mul_one, union_empty] at h
  rw [allEven_eq_fin]
  exact h
end VariableBound.StepParity
