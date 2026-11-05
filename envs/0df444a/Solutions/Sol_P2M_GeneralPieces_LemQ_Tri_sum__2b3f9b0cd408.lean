-- Prove2me | solution 1 for P2M_GeneralPieces_LemQ_Tri_sum__2b3f9b0cd408
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:13:00.467683+00:00
-- url     : https://prove2.me/submissions/3f551ffa-3105-4fc1-aa54-916fc4b0a589

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_P2M_GeneralPieces_LemQ_Tri_zero__075e2eaa1ffc

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.LemQ.Tri
variable {T T' : V → V → V → V}
namespace GeneralPieces.LemQ.Tri
theorem _root_.solution (hT : Tri T) (S : Finset Ptn) (q : Ptn → ℚ) (a b : V) : T a b (∑ μ ∈ S, q μ • tpow μ) = ∑ μ ∈ S, q μ • T a b (tpow μ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hT.zero₃]
  | insert x S hx ih => rw [sum_insert hx, sum_insert hx, hT.add₃, hT.smul₃, ih]
end GeneralPieces.LemQ.Tri
