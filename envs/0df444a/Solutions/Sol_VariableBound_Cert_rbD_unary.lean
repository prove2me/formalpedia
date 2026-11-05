-- Prove2me | solution 1 for VariableBound.Cert.rbD_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:33:26.924693+00:00
-- url     : https://prove2.me/submissions/2a128588-f17b-4478-af48-8a91a683c7d1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Params_Cert
import Theorems.Thm_VariableBound_Cert_filter_range_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_min_right
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_min_right
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_two_pow
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open VariableBound
open Groundwork AppVariables PaddedDescent.F ClauseBound.ParityChecks.CertLib
open VariableBound.Cert
variable {α : Type} [Enc α]
namespace VariableBound.Cert
theorem _root_.solution {β : α → ℕ} (hβ : Unary β) : Unary fun x => rbD (β x) := by
  have hN : Unary fun x => 3 * β x + 2 := ((Unary.const 3).mul hβ).add (Unary.const 2)
  have hmin : Unary fun p : α × ℕ => min p.2 (3 * β p.1 + 2) := unary_min_right PolyT.id'.snd (hN.comp PolyT.id'.fst)
  exact Unary.of_length (filter_range_polyT (f := fun x j => decide (¬ 3 ^ j * 2 ^ β x < 4 ^ j)) hN
    (PolyT.decide_not (PolyT.decide_lt ((PolyT.pow_unary (PolyT.const 3) hmin).mul (PolyT.two_pow (hβ.comp PolyT.id'.fst))) (PolyT.pow_unary (PolyT.const 4) hmin))))
end VariableBound.Cert
