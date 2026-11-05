-- Prove2me | solution 1 for P2M_GeneralPieces_LemQ_Tri_zero__075e2eaa1ffc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:12:02.433982+00:00
-- url     : https://prove2.me/submissions/8976b476-2893-4fcb-a7ed-d5e45ef6a5eb

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
theorem _root_.solution (hT : Tri T) (a b : V) : T a b 0 = 0 := by
  have := hT.smul₃ 0 a b 0
  simpa using this
end GeneralPieces.LemQ.Tri
