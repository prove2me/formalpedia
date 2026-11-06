-- Prove2me | solution 1 for PairsToBound.atWidthOr3_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:14:09.766621+00:00
-- url     : https://prove2.me/submissions/c1bf4d26-f9b0-4e5c-ba69-9a848b2fed40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_FrontEnd
import Theorems.Thm_PairsToBound_widthN_unary
import Theorems.Thm_ClauseBound_Alg_Decode_stCertDecM
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_VariableBound_Rename_encN_polyT
attribute [local fun_prop] Groundwork.PolyT.snd



set_option autoImplicit false
section
section
open PairsToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg MainTheoremForms VariableBound.Rename
open Sat3 (CNF)
variable {α : Type} [Enc α]
namespace PairsToBound
theorem _root_.solution : PolyT atWidthOr3 :=
  encN_polyT (widthN_unary Decode.stCertDecM.2.snd) Decode.stCertDecM.2
end PairsToBound
