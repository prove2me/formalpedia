-- Prove2me | solution 1 for SparsificationLemma.Mach.Cert.polyT_dL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:38.308584+00:00
-- url     : https://prove2.me/submissions/71d81718-cffd-4143-bd65-66b2312cd0ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Walk
import Definitions.Def_UniformInK_Cert_Walk
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_SparsificationLemma_Mach_Cert
import Theorems.Thm_ClauseBound_Alg_Decode_restOf_polyT
import Theorems.Thm_ClauseBound_Alg_Decode_stCertDecM
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_Unary_comp
attribute [local fun_prop] Groundwork.PolyT.comp



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach SparsificationLemma.Mach.Cert
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly CountKSatRate CountKSatRate.Cert UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg
variable {α σ : Type} [Enc α]
namespace SparsificationLemma.Mach.Cert
theorem _root_.solution : PolyT dL := PolyT.comp (f := fmlOf) (g := restOf) Decode.stCertDecM.2 Decode.restOf_polyT
end SparsificationLemma.Mach.Cert
