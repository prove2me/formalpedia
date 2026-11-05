-- Prove2me | solution 1 for VariableBound.Rename.numOcc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:12.845183+00:00
-- url     : https://prove2.me/submissions/58763a4a-6905-4b97-b6ea-b5211ce70cd5

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

set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)
variable {N : ℕ} (φ : CNF N)
namespace VariableBound.Rename
theorem _root_.solution : numOcc φ ≤ N := by
  have h := Nat.card_le_card_of_injective (Subtype.val : {i : Fin N // Occurs φ i} → Fin N) Subtype.val_injective
  rwa [Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin] at h
end VariableBound.Rename
