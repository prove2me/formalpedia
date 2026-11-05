-- Prove2me | solution 1 for PaddedDescent.F.CertTop.sOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:21:47.954969+00:00
-- url     : https://prove2.me/submissions/0d49d8c9-c6fb-4f09-bd7f-d476a189513f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_CertSparsify
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_PaddedDescent_F_CertTop
import Theorems.Thm_PaddedDescent_F_CertTop_two_pow_sOf_le

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Sparsify
open WidthK (theta)
open WidthK.Prog (stepK)
variable {α : Type} [Enc α]
namespace PaddedDescent.F.CertTop
theorem _root_.solution (n : ℕ) : sOf n ≤ n := by
  have h1 := two_pow_sOf_le n
  have h2 : sOf n < 2 ^ sOf n := Nat.lt_two_pow_self
  omega
end PaddedDescent.F.CertTop
