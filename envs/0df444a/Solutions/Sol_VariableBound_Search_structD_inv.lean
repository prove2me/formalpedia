-- Prove2me | solution 1 for VariableBound.Search.structD_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:10:59.633923+00:00
-- url     : https://prove2.me/submissions/66efd1ee-93a0-4db8-a471-ab0a2163dcb7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Defs
import Definitions.Def_VariableBound_StepChoice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Search_Correct
import Theorems.Thm_VariableBound_Search_structD_of
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_VariableBound_stepChoice
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F AppVariables Finset
variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (n nb rb tb : ℕ) (fam : List (List ℕ))
variable {V n nb rb tb fam}
namespace VariableBound.Search
theorem _root_.solution (H : Hyp X m n nb rb tb fam) (L : List (List ℕ)) (hL : Inv V n nb rb tb fam L) : StructD m nb rb tb L := by
  refine structD_of H L hL.1 ?_
  have := stepChoice.structure_ X (Fin m) (Fin fam.length) V n nb rb tb univ (fun i => Fld.setD m (fam.get i)) (chksD m L) (chksD m L) H.hX H.hnb
  rw [Fintype.card_fin] at this ⊢
  exact this H.hrb H.htb H.hF hL.2 (Or.inl rfl)
end VariableBound.Search
