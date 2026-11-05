-- Prove2me | solution 1 for P2M_GeneralPieces_LemQ_Tri_zero__082fda2dbba7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:11:34.697685+00:00
-- url     : https://prove2.me/submissions/c517e0b9-186a-4149-9809-109b4427065f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.LemQ.Tri
variable {T T' : V → V → V → V}
namespace GeneralPieces.LemQ.Tri
theorem _root_.solution (hT : Tri T) (b f : V) : T 0 b f = 0 := by
  have := hT.smul₁ 0 0 b f
  simpa using this
end GeneralPieces.LemQ.Tri
