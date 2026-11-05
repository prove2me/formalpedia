-- Prove2me | solution 1 for VariableBound.Rename.numSat_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:34:52.678512+00:00
-- url     : https://prove2.me/submissions/68e6e629-a16d-466d-99bc-817b5e382616

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_VariableBound_Paper_Rename_Math
import Theorems.Thm_VariableBound_Rename_card_not_occurs
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)
variable {N : ℕ} (φ : CNF N)
namespace VariableBound.Rename
theorem _root_.solution : SatK.numSat φ = 2 ^ (N - numOcc φ) * numSatOcc φ := by
  classical
  rw [SatK.numSat, numSatOcc, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← card_not_occurs, mul_comm]
  have e1 : {a : Fin N → Bool // ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2} ≃
      {p : ({i : Fin N // Occurs φ i} → Bool) × ({i : Fin N // ¬ Occurs φ i} → Bool) // ∀ C ∈ φ, ∃ l ∈ C, ∃ h : Occurs φ l.1, p.1 ⟨l.1, h⟩ = l.2} :=
    (Equiv.piEquivPiSubtypeProd (Occurs φ) fun _ => Bool).subtypeEquiv fun a => by
      refine forall₂_congr fun C hC => ⟨?_, ?_⟩
      · rintro ⟨l, hl, h⟩
        exact ⟨l, hl, ⟨C, hC, l, hl, rfl⟩, h⟩
      · rintro ⟨l, hl, _, h⟩
        exact ⟨l, hl, h⟩
  rw [Nat.card_congr (e1.trans (Equiv.prodSubtypeFstEquivSubtypeProd
    (p := fun b : {i : Fin N // Occurs φ i} → Bool => ∀ C ∈ φ, ∃ l ∈ C, ∃ h : Occurs φ l.1, b ⟨l.1, h⟩ = l.2))), Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
end VariableBound.Rename
