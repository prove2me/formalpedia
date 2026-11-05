-- Prove2me | solution 1 for P2M_GeneralPieces_LemQ_tri_Q__731a24d79bc8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:13:21.73597+00:00
-- url     : https://prove2.me/submissions/aced890a-efe9-49ba-9170-8c72fcf239cd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_Tri_smul
import Theorems.Thm_GeneralPieces_LemQ_tri_ba

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (hOp : OpFacts) (h : ℕ) (s : ℤ) : Tri (Q' h s) := Tri.sum _ fun i => (tri_ba hOp h i _ _).smul _
end GeneralPieces.LemQ
