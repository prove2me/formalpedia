-- Prove2me | solution 1 for P2M_GeneralPieces_LemQ_Tri_sum__d29a426cc3fb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:12:50.649182+00:00
-- url     : https://prove2.me/submissions/dfdd70f0-ae7f-43de-bde2-b4f4d86af9b4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_P2M_GeneralPieces_LemQ_Tri_zero__082fda2dbba7

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.LemQ.Tri
variable {T T' : V → V → V → V}
namespace GeneralPieces.LemQ.Tri
theorem _root_.solution (hT : Tri T) (S : Finset Ptn) (q : Ptn → ℚ) (b f : V) : T (∑ μ ∈ S, q μ • tpow μ) b f = ∑ μ ∈ S, q μ • T (tpow μ) b f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hT.zero₁]
  | insert x S hx ih => rw [sum_insert hx, sum_insert hx, hT.add₁, hT.smul₁, ih]
end GeneralPieces.LemQ.Tri
