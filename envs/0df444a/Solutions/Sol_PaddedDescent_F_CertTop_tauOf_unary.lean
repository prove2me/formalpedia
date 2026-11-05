-- Prove2me | solution 1 for PaddedDescent.F.CertTop.tauOf_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:53:29.990915+00:00
-- url     : https://prove2.me/submissions/5d9f5528-2e00-412d-b714-1dfef0baf95d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_CertSparsify
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_PaddedDescent_F_CertTop
import Theorems.Thm_PaddedDescent_F_CertTop_two_pow_lin_unary

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Sparsify
open WidthK (theta)
open WidthK.Prog (stepK)
variable {α : Type} [Enc α]
namespace PaddedDescent.F.CertTop
theorem _root_.solution {n : α → ℕ} (hn : Unary n) : Unary fun x => tauOf (sOf (n x)) := by
  unfold tauOf
  exact two_pow_lin_unary 4 17 hn
end PaddedDescent.F.CertTop
