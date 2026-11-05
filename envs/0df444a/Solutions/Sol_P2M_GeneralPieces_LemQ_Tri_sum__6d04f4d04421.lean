-- Prove2me | solution 1 for P2M_GeneralPieces_LemQ_Tri_sum__6d04f4d04421
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:12:53.742122+00:00
-- url     : https://prove2.me/submissions/665cf61d-6fd7-456c-a84f-e020cd656345

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_P2M_GeneralPieces_LemQ_Tri_zero__dd41a61eba46

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.LemQ.Tri
variable {T T' : V → V → V → V}
namespace GeneralPieces.LemQ.Tri
theorem _root_.solution (hT : Tri T) (S : Finset Ptn) (q : Ptn → ℚ) (a f : V) : T a (∑ μ ∈ S, q μ • tpow μ) f = ∑ μ ∈ S, q μ • T a (tpow μ) f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hT.zero₂]
  | insert x S hx ih => rw [sum_insert hx, sum_insert hx, hT.add₂, hT.smul₂, ih]
end GeneralPieces.LemQ.Tri
