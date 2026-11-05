-- Prove2me | solution 1 for PaddedDescent.F.Mark.Cert.neg_one_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:25:39.360832+00:00
-- url     : https://prove2.me/submissions/c506b99c-1bd6-4c3c-9b1f-6f413a932e47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_PaddedDescent_F_CertMark

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Cert
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]
namespace PaddedDescent.F.Mark.Cert
theorem _root_.solution (k : ℕ) : (-1 : ℤ) ^ k = if k % 2 = 0 then 1 else -1 := by
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow, if_pos (Nat.even_iff.1 h)]
  · rw [h.neg_one_pow, if_neg (by rw [Nat.odd_iff.1 h]; decide)]
end PaddedDescent.F.Mark.Cert
