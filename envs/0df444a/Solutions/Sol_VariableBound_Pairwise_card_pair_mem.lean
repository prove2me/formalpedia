-- Prove2me | solution 1 for VariableBound.Pairwise.card_pair_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:46:23.565536+00:00
-- url     : https://prove2.me/submissions/1b9a378e-51d6-4ebd-b500-9a13fd36916f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_VariableBound_Family_Pairwise
import Theorems.Thm_VariableBound_Pairwise_pair_uniform

set_option autoImplicit false
section
section
open VariableBound VariableBound.Pairwise
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
omit [Algebra (ZMod 2) F]
namespace VariableBound.Pairwise
theorem _root_.solution (θ θ' : F) (h : θ ≠ θ') (S : Finset (F × F)) : #{p : F × F | (p.1 * θ + p.2, p.1 * θ' + p.2) ∈ S} = #S :=
  card_equiv (Equiv.ofBijective _ (pair_uniform θ θ' h)) fun p => by simp
end VariableBound.Pairwise
