-- Prove2me | solution 1 for P2M_GeneralPieces_Ring_map_toPNat__toN_169eea647133
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:30:08.121146+00:00
-- url     : https://prove2.me/submissions/3fe5b3ff-5866-42e9-854b-fe65d4a7945e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : Ptn) : (toN μ).map Nat.toPNat' = μ := by
  unfold toN
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id μ]
  exact Multiset.map_congr rfl fun k _ => PNat.coe_toPNat' k
end GeneralPieces.Ring
