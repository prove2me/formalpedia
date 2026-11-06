-- Prove2me | solution 1 for VariableBound.Net.Tuples.back_subset_vset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:54:55.28483+00:00
-- url     : https://prove2.me/submissions/9f5923b5-f43b-4513-a136-8c2f43b2b6bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_Net_Tuples
import Theorems.Thm_VariableBound_Net_Tuples_mem_back
import Theorems.Thm_VariableBound_Net_Tuples_mem_Vof
import Theorems.Thm_VariableBound_Net_Tuples_mem_vset
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Tuples
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
open ClauseBound.ParityChecks (Vof)
variable {k n : ℕ} {D : Dat}
namespace VariableBound.Net.Tuples
theorem _root_.solution {σ : Fin n → Bool} {r : ℕ} {S₀ : Finset (Fin D.1.length)} {S : Fin r → Finset (Fin D.1.length)}
    (h0 : S₀ ⊆ Vof D.1 σ) (h1 : ∀ j, S j ⊆ Vof D.1 σ) : back D S₀ S ⊆ vset (Mark.ext σ) D := by
  intro o ho
  obtain ⟨hlt, ⟨e, he, hx⟩ | ⟨j, e, he, hx⟩⟩ := mem_back.1 ho
  · exact mem_vset.2 ⟨hlt, by rw [hx]; exact mem_Vof.1 (h0 he)⟩
  · exact mem_vset.2 ⟨hlt, by rw [hx]; exact mem_Vof.1 (h1 j he)⟩
end VariableBound.Net.Tuples
