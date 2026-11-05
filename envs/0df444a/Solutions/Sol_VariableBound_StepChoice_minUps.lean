-- Prove2me | solution 1 for VariableBound.StepChoice.minUps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:39:22.604855+00:00
-- url     : https://prove2.me/submissions/2d311a67-274c-463c-a400-1f28c12b1383

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_StepChoice
import Theorems.Thm_VariableBound_StepChoice_avgUps

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace VariableBound.StepChoice
theorem _root_.solution (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hnb : 1 ≤ nb) (hF : IsFamily nb Ω Γ)
    (hr : L.length < rb) (u : ι) (hu : u ∈ Ω) (hmin : ∀ u' ∈ Ω, Ups V nb β rb tb (L ++ [Γ u]) ≤ Ups V nb β rb tb (L ++ [Γ u'])) :
    Ups V nb β rb tb (L ++ [Γ u]) ≤ Ups V nb β rb tb L := by
  have h0 : (0 : ℚ) < #Ω := by exact_mod_cast card_pos.2 ⟨u, hu⟩
  have h1 : #Ω • Ups V nb β rb tb (L ++ [Γ u]) ≤ ∑ u' ∈ Ω, Ups V nb β rb tb (L ++ [Γ u']) := card_nsmul_le_sum _ _ _ hmin
  rw [nsmul_eq_mul] at h1
  exact le_of_mul_le_mul_left (h1.trans (avgUps V nb β rb tb Ω Γ L hnb hF hr)) h0
end VariableBound.StepChoice
