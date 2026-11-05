-- Prove2me | solution 1 for VariableBound.Search.structD_more
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:33:37.875819+00:00
-- url     : https://prove2.me/submissions/2184544c-2623-4a65-be1d-d8e1ec7e8ae1

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
import Theorems.Thm_VariableBound_Search_chksD_append
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
theorem _root_.solution (H : Hyp X m n nb rb tb fam) (L : List (List ℕ)) (hL : Inv V n nb rb tb fam L) (hpos : 0 < Xsum V nb (chksD m L)) (l : List ℕ) (hl : l ∈ fam) :
    StructD m nb rb tb (L ++ [l]) := by
  refine structD_of H (L ++ [l]) ?_ ?_
  · intro l' h'
    rcases List.mem_append.1 h' with h' | h'
    · exact hL.1 l' h'
    · rw [List.mem_singleton.1 h']; exact hl
  · obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
    have := stepChoice.structure_ X (Fin m) (Fin fam.length) V n nb rb tb univ (fun i => Fld.setD m (fam.get i)) (chksD m L) (chksD m (L ++ [fam.get i])) H.hX H.hnb
    rw [Fintype.card_fin] at this ⊢
    exact this H.hrb H.htb H.hF hL.2 (Or.inr ⟨hpos, i, mem_univ i, chksD_append m L _⟩)
end VariableBound.Search
