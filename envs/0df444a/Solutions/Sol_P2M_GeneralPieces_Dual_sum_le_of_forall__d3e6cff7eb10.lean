-- Prove2me | solution 1 for P2M_GeneralPieces_Dual_sum_le_of_forall__d3e6cff7eb10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:19:40.173195+00:00
-- url     : https://prove2.me/submissions/0cb12a51-b67a-4bd0-8ce6-ba545506c56b

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
theorem _root_.solution (μ : List ℕ+) (ks : List ℤ) (h : List.Forall₂ (fun (n : ℕ+) (k : ℤ) => (n : ℤ) ≤ k) μ ks) :
    (μ.map fun n : ℕ+ => (n : ℤ)).sum ≤ ks.sum := by
  induction h with
  | nil => simp
  | cons h1 _ ih => simp only [List.map_cons, List.sum_cons]; omega
end GeneralPieces.Dual
