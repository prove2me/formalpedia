-- Prove2me | solution 1 for SparsificationLemma.Mach.Cert.polyT_eL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:34:35.673911+00:00
-- url     : https://prove2.me/submissions/a781dbd5-6560-4aa8-89df-73153669c353

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Walk
import Definitions.Def_UniformInK_Cert_Walk
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_SparsificationLemma_Mach_Cert
import Theorems.Thm_SparsificationLemma_Mach_Cert_unary_sL
import Theorems.Thm_SparsificationLemma_Mach_Cert_unary_kL
import Theorems.Thm_SparsificationLemma_Mach_Cert_polyT_dL
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach SparsificationLemma.Mach.Cert
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly CountKSatRate CountKSatRate.Cert UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg
variable {α σ : Type} [Enc α]
namespace SparsificationLemma.Mach.Cert
theorem _root_.solution : PolyT eL := by
  have h1 : PolyT fun x : List Bool => 2 ^ sL x := pow_polyT (PolyT.const 2) unary_sL
  have h2 : PolyT fun x : List Bool => (dL x).1.length := (Unary.of_length polyT_dL.fst).poly
  have h3 : PolyT fun x : List Bool => Nat.size x.length := PolyT.size' (Unary.of_length PolyT.id').poly
  exact (((PolyT.div h2 h1).add unary_kL.poly).add ((PolyT.const 3).mul h3)).add (PolyT.const 9)
end SparsificationLemma.Mach.Cert
