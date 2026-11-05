-- Prove2me | solution 1 for P2M_GeneralPieces_Dual_forall__replicate_53e3e372b2d2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:16:15.769555+00:00
-- url     : https://prove2.me/submissions/9af64992-1a89-42a7-a5df-768066da0a66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution {α : Type} (S : Finset α) (r : ℕ) (x : List α) :
    List.Forall₂ (fun a s => a ∈ s) x (List.replicate r S) ↔ x.length = r ∧ ∀ a ∈ x, a ∈ S := by
  induction r generalizing x with
  | zero => cases x <;> simp
  | succ r ih =>
    cases x with
    | nil => simp [List.replicate_succ]
    | cons a x => simp [List.replicate_succ, ih, and_left_comm]
end GeneralPieces.Dual
