-- Prove2me | solution 1 for P2M_GeneralPieces_Ring_toN_map_toPNat__be122ac80f3b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:30:09.840615+00:00
-- url     : https://prove2.me/submissions/fb9a2f9a-d323-46e3-8f3d-845b483d17e7

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
theorem _root_.solution {s : Multiset ℕ} (hs : ∀ i ∈ s, 0 < i) : toN (s.map Nat.toPNat') = s := by
  unfold toN
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id s]
  exact Multiset.map_congr rfl fun k hk => PNat.toPNat'_coe (hs k hk)
end GeneralPieces.Ring
