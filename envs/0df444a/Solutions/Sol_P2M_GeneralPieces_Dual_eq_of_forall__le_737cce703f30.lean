-- Prove2me | solution 1 for P2M_GeneralPieces_Dual_eq_of_forall__le_737cce703f30
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:20:55.406593+00:00
-- url     : https://prove2.me/submissions/77c402d8-bcab-4890-8677-6a824d46ddbe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_P2M_GeneralPieces_Dual_sum_le_of_forall__d3e6cff7eb10

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (μ : List ℕ+) (ks : List ℤ) (h : List.Forall₂ (fun (n : ℕ+) (k : ℤ) => (n : ℤ) ≤ k) μ ks)
    (hs : ks.sum = (μ.map fun n : ℕ+ => (n : ℤ)).sum) : ks = μ.map fun n : ℕ+ => (n : ℤ) := by
  induction h with
  | nil => rfl
  | cons h1 h2 ih =>
    have h3 := sum_le_of_forall₂ _ _ h2
    rw [List.map_cons, List.sum_cons, List.sum_cons] at hs
    rw [List.map_cons, ← ih (by omega)]
    congr 1
    omega
end GeneralPieces.Dual
