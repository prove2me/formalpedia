-- Prove2me | solution 1 for VariableBound.Count.Vof_eq_empty_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:45:07.621293+00:00
-- url     : https://prove2.me/submissions/08b3bffc-652c-41fb-a9de-a72129a45bf5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct
import Theorems.Thm_VariableBound_Count_not_vio_iff
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset
namespace VariableBound.Count
theorem _root_.solution {n : ℕ} (ψ : Fml) (ξ : Fin n → Bool) : Vof ψ ξ = ∅ ↔ ∀ C ∈ ψ, ∃ l ∈ C, Mark.ext ξ l.1 = l.2 := by
  rw [Vof, filter_eq_empty_iff]
  constructor
  · intro H C hC
    obtain ⟨e, he, rfl⟩ := List.mem_iff_getElem.1 hC
    have h1 := H (mem_univ (⟨e, he⟩ : Fin ψ.length))
    rw [List.getD_eq_getElem _ _ he] at h1
    exact (not_vio_iff _ _).1 h1
  · intro H e _
    have h1 := H _ (List.getElem_mem e.2)
    rw [List.getD_eq_getElem _ _ e.2]
    exact (not_vio_iff _ _).2 h1
end VariableBound.Count
