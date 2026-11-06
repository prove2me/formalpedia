-- Prove2me | solution 1 for StepSparsify.CertThCal.catalan_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:47:25.486056+00:00
-- url     : https://prove2.me/submissions/c9992f4f-a9d5-40d2-a126-22a709ac6db9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Mathlib.Data.Nat.Choose.Central
import Definitions.Def_StepSparsify_CertThCal
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_choose_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.mul



set_option autoImplicit false
section
section
open StepSparsify StepSparsify.CertThCal
open Groundwork SparsificationLemma ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace StepSparsify.CertThCal
theorem _root_.solution {c : α → ℕ} (hc : Unary c) : PolyT fun x => catalan (c x) :=
  (PolyT.div (choose_polyT (PolyT.mul (PolyT.const 2) hc.poly) hc) (PolyT.add hc.poly (PolyT.const 1))).congr fun x => by
    rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]
end StepSparsify.CertThCal
