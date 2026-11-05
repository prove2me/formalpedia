-- Prove2me | solution 1 for VariableBound.Search.ups_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:09:25.216714+00:00
-- url     : https://prove2.me/submissions/3f6929d2-f12c-4675-88dd-d9e48e77d977

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
import Theorems.Thm_VariableBound_Search_length_chksD
import Theorems.Thm_VariableBound_Search_sum_load
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.div_pow
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F AppVariables Finset
namespace VariableBound.Search
theorem _root_.solution {X : Type} [Fintype X] (m : ℕ) (V : X → Finset (Fin m)) (nb β rb tb : ℕ) (L : List (List ℕ)) (hnb : 1 ≤ nb) :
    Ups V nb β rb tb (chksD m L) = (upsNum m nb β rb tb (Xsum V nb (chksD m L)) L : ℚ) / den nb β rb tb L.length := by
  have h0 : (0 : ℚ) < nb := by exact_mod_cast hnb
  unfold Ups upsNum den pp
  rw [sum_load, length_chksD]
  have h1 : (1 + 16 / (15 * (nb : ℚ))) = (15 * nb + 16) / (15 * nb) := by field_simp
  rw [h1, div_pow, div_pow]
  push_cast
  field_simp
end VariableBound.Search
