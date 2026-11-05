-- Prove2me | solution 1 for SparsificationLemma.Mach.Cert.unary_sL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:56:07.18693+00:00
-- url     : https://prove2.me/submissions/704c4a0f-d2ae-421b-8a1d-04fdeee0f62b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Walk
import Definitions.Def_UniformInK_Cert_Walk
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_SparsificationLemma_Mach_Cert
import Theorems.Thm_ClauseBound_Alg_Decode_kOf_polyT
import Theorems.Thm_Groundwork_Unary_of_length


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach SparsificationLemma.Mach.Cert
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly CountKSatRate CountKSatRate.Cert UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg
variable {α σ : Type} [Enc α]
namespace SparsificationLemma.Mach.Cert
theorem _root_.solution : Unary sL := Unary.of_length Decode.kOf_polyT
end SparsificationLemma.Mach.Cert
