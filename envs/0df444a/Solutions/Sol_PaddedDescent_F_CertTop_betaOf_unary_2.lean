-- Prove2me | solution 2 for PaddedDescent.F.CertTop.betaOf_unary
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:25:36.183503+00:00
-- url     : https://prove2.me/submissions/e23e7fca-d134-4130-86d5-912e8cc0e8ea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_CertSparsify
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_PaddedDescent_F_CertTop
import Theorems.Thm_PaddedDescent_F_CertTop_sOf_unary
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Sparsify
open WidthK (theta)
open WidthK.Prog (stepK)
variable {α : Type} [Enc α]
attribute [local fun_prop] PaddedDescent.F.CertTop.sOf_unary

theorem solution {n : α → ℕ} (hn : Unary n) : Unary fun x => betaOf (sOf (n x)) := by
  unfold betaOf
  fun_prop
