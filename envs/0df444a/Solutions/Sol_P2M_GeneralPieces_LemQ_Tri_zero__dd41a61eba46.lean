-- Prove2me | solution 1 for P2M_GeneralPieces_LemQ_Tri_zero__dd41a61eba46
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:11:42.590819+00:00
-- url     : https://prove2.me/submissions/14521055-5099-4661-9bde-cbd0b4325edd

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
theorem _root_.solution (hT : Tri T) (a f : V) : T a 0 f = 0 := by
  have := hT.smul₂ 0 a 0 f
  simpa using this
end GeneralPieces.LemQ.Tri
