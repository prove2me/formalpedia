-- Prove2me | solution 1 for StepSparsify.CertThCal.stCertThCal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:48:54.977441+00:00
-- url     : https://prove2.me/submissions/130879a2-fedd-446f-bd6f-f79674cbf080

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Mathlib.Data.Nat.Choose.Central
import Definitions.Def_StepSparsify_CertThCal
import Theorems.Thm_StepSparsify_CertThCal_thetaC_polyT
import Theorems.Thm_StepSparsify_CertThCal_alphaS_polyT
import Theorems.Thm_Groundwork_Unary_poly


set_option autoImplicit false
section
section
open StepSparsify StepSparsify.CertThCal
open Groundwork SparsificationLemma ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace StepSparsify.CertThCal
theorem _root_.solution (hA : StAlphaS) : StCertThCal := fun _ _ _ _ _ hk hs hi => thetaC_polyT (alphaS_polyT hA hk.poly hs) hi
end StepSparsify.CertThCal
