-- Prove2me | solution 1 for StepSparsify.CertThCal.thetaC_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:47:17.943194+00:00
-- url     : https://prove2.me/submissions/44aa58d3-73e6-45e9-a127-03bc557d7119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Mathlib.Data.Nat.Choose.Central
import Definitions.Def_StepSparsify_CertThCal
import Theorems.Thm_SparsificationLemma_Cal_stBetaCat


set_option autoImplicit false
section
section
open StepSparsify StepSparsify.CertThCal
open Groundwork SparsificationLemma ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace StepSparsify.CertThCal
theorem _root_.solution (a i : ℕ) : Cal.thetaC a i = if i = 0 then 2 else a * (2 * (8 * a) ^ (i - 1) * catalan (i - 1)) := by
  cases i with
  | zero => rfl
  | succ i => rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, ← Cal.stBetaCat a i]; rfl
end StepSparsify.CertThCal
