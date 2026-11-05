-- Prove2me | solution 1 for P2M_GeneralPieces_Group_le_B_of_b549728d8dae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:44:03.986876+00:00
-- url     : https://prove2.me/submissions/2aa6ecb3-cb0b-4294-850f-1fd5b6c16d45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_CaseI
import Definitions.Def_GeneralPieces_Group_CaseII
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_CertG
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_GeneralPieces_Group_Lemma

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset Groundwork
variable {J J' σ τ A : Type*}
open Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F PaddedDescent.F.RebalF PaddedDescent.Col
namespace GeneralPieces.Group
theorem _root_.solution (K g P B : ℕ) (hK : 0 < K) : P * (2 * g / K) + B * g ^ 2 ≤ AppRunningTime.B'of K g P B := by
  unfold AppRunningTime.B'of
  have h1 : P * (2 * g / K) ≤ (2 * g * P + K - 1) / K := by
    rw [Nat.le_div_iff_mul_le hK]
    calc P * (2 * g / K) * K = P * (2 * g / K * K) := by ring
      _ ≤ P * (2 * g) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ ≤ 2 * g * P + K - 1 := by rw [Nat.mul_comm]; omega
  rw [Nat.mul_comm B]
  omega
end GeneralPieces.Group
