-- Prove2me | solution 1 for PaddedDescent.F.Mark.Cert.sign_polyT
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:39:44.1472+00:00
-- url     : https://prove2.me/submissions/ad4506ca-c77b-4089-8989-b883f23db406

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

private theorem neg_one_pow_eq (k : ℕ) : (-1 : ℤ) ^ k = if k % 2 = 0 then 1 else -1 := by
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow, if_pos (Nat.even_iff.1 h)]
  · rw [h.neg_one_pow, if_neg (by rw [Nat.odd_iff.1 h]; decide)]

theorem solution {k : α → ℕ} (hk : PolyT k) : PolyT fun x => (-1 : ℤ) ^ k x := by
  simp only [neg_one_pow_eq]
  have hmod : PolyT fun x => k x % 2 := PolyT.mod hk (PolyT.const 2)
  exact PolyT.ite' (PolyT.decide_eq hmod (PolyT.const 0)) (PolyT.const 1) (PolyT.const (-1))
