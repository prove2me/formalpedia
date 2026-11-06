-- Prove2me | solution 1 for VariableBound.Count.modZ_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:46:06.682656+00:00
-- url     : https://prove2.me/submissions/2c35a930-6ecd-4c1f-a170-c5e1670d242e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Count_Cert
import Theorems.Thm_VariableBound_Count_emod_natCast
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mod
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219



set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg AppVariables VariableBound.Net
variable {α : Type} [Enc α]
namespace VariableBound.Count
theorem _root_.solution {a : α → ℤ} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => a x % (b x : ℤ) := by
  have h1 : PolyT fun x => (a x).toNat % b x := PolyT.mod (PolyT.toNat ha) hb
  have h2 : PolyT fun x => b x - 1 - ((a x).natAbs - 1) % b x :=
    PolyT.sub (PolyT.sub hb (PolyT.const 1)) (PolyT.mod (PolyT.sub (PolyT.natAbs ha) (PolyT.const 1)) hb)
  exact (PolyT.ite' (PolyT.decide_leZ (PolyT.const 0) ha) (PolyT.natCast h1)
    (PolyT.ite' (PolyT.decide_eq hb (PolyT.const 0)) ha (PolyT.natCast h2))).congr fun x => (emod_natCast _ _).symm
end VariableBound.Count
