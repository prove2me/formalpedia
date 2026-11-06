-- Prove2me | solution 1 for RecursionToBound.alphaC_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:27:24.73896+00:00
-- url     : https://prove2.me/submissions/1770a35b-16d8-4217-8db7-124e8f370376

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
import Theorems.Thm_RecursionToBound_alphaN_polyT
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_RecursionToBound_alphaC_epsOf


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert UniformInK UniformInK.CertSparsify SparsificationLemma
variable {α : Type} [Enc α]
namespace RecursionToBound
theorem _root_.solution {k : α → ℕ} {r : α → ℕ × ℕ} (hk : PolyT k) (hr : PolyT r) : PolyT fun x => Cal.alphaC (k x) (epsOf (r x)) :=
  (alphaN_polyT hk hr).congr fun x => (alphaC_epsOf (k x) (r x)).symm
end RecursionToBound
