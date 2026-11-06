-- Prove2me | solution 1 for VariableBound.Count.mod_two_pow_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:53:34.745196+00:00
-- url     : https://prove2.me/submissions/faffc8f6-ec23-41a0-aecf-4d27540e051d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Count_Cert
import Theorems.Thm_VariableBound_Count_modZ_polyT
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg AppVariables VariableBound.Net
variable {α : Type} [Enc α]
namespace VariableBound.Count
theorem _root_.solution {a : α → ℤ} {k : α → ℕ} (ha : PolyT a) (hk : Unary k) : PolyT fun x => a x % 2 ^ k x :=
  (modZ_polyT ha (PolyT.pow_unary (PolyT.const 2) hk)).congr fun x => by push_cast; rfl
end VariableBound.Count
