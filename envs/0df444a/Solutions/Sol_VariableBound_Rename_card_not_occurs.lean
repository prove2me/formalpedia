-- Prove2me | solution 1 for VariableBound.Rename.card_not_occurs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:13.904183+00:00
-- url     : https://prove2.me/submissions/03fded9e-de4f-4ab8-bdf5-e98f6a053a96

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
theorem _root_.solution : Nat.card {i : Fin N // ¬ Occurs φ i} = N - numOcc φ := by
  classical
  rw [numOcc, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin]
end VariableBound.Rename
