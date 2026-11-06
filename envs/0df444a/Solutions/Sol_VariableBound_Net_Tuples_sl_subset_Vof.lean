-- Prove2me | solution 1 for VariableBound.Net.Tuples.sl_subset_Vof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:01:53.701878+00:00
-- url     : https://prove2.me/submissions/d735f521-d94b-46d2-844b-e4dec3cc4c99

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
import Theorems.Thm_VariableBound_Net_Tuples_mem_sl
import Theorems.Thm_VariableBound_Net_Tuples_mem_Vof
import Theorems.Thm_VariableBound_Net_Tuples_mem_vset

set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Tuples
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
open ClauseBound.ParityChecks (Vof)
variable {k n : ℕ} {D : Dat}
namespace VariableBound.Net.Tuples
theorem _root_.solution {σ : Fin n → Bool} {P : Finset ℕ} (hP : P ⊆ vset (Mark.ext σ) D) (κ j : ℕ) : sl D κ j P ⊆ Vof D.1 σ := by
  intro e he
  obtain ⟨o, ho, hx⟩ := mem_sl.1 he
  have h := (mem_vset.1 (hP ho)).2
  rw [hx] at h
  exact mem_Vof.2 h
end VariableBound.Net.Tuples
