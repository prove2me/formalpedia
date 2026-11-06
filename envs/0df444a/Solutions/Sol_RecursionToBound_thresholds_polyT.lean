-- Prove2me | solution 1 for RecursionToBound.thresholds_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:41:58.572716+00:00
-- url     : https://prove2.me/submissions/73a51421-a228-4284-bb94-4e12f5f8390b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_StepSparsify_CertThCal
import Definitions.Def_UniformInK_Cert_Sparsify
import Definitions.Def_CountKSat_Poly
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_RecursionToBound_Cert_Thresholds
import Theorems.Thm_RecursionToBound_alphaC_polyT
import Theorems.Thm_StepSparsify_CertThCal_thetaC_polyT


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert UniformInK UniformInK.CertSparsify SparsificationLemma
variable {α : Type} [Enc α]
namespace RecursionToBound
theorem _root_.solution {k i : α → ℕ} {r : α → ℕ × ℕ} (hk : PolyT k) (hr : PolyT r) (hi : Unary i) : PolyT fun x => thresholds (k x) (r x) (i x) :=
  _root_.StepSparsify.CertThCal.thetaC_polyT (alphaC_polyT hk hr) hi
end RecursionToBound
