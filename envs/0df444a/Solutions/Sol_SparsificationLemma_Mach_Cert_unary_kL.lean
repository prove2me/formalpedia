-- Prove2me | solution 1 for SparsificationLemma.Mach.Cert.unary_kL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:57:40.743942+00:00
-- url     : https://prove2.me/submissions/5beb6f98-1524-4120-8b4d-7de47e021419

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Walk
import Definitions.Def_UniformInK_Cert_Walk
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_SparsificationLemma_Mach_Cert
import Theorems.Thm_ClauseBound_Alg_Decode_kOf_polyT
import Theorems.Thm_ClauseBound_Alg_Decode_restOf_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_of_length
attribute [local fun_prop] Groundwork.PolyT.comp



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach SparsificationLemma.Mach.Cert
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly CountKSatRate CountKSatRate.Cert UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg
variable {α σ : Type} [Enc α]
namespace SparsificationLemma.Mach.Cert
theorem _root_.solution : Unary kL := Unary.of_length (PolyT.comp (f := kOf) (g := restOf) Decode.kOf_polyT Decode.restOf_polyT)
end SparsificationLemma.Mach.Cert
