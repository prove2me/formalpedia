-- Prove2me | solution 1 for PairsToBound.atWidthOr3_rewrites
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:49:03.17487+00:00
-- url     : https://prove2.me/submissions/ddfc9cdc-22d3-49be-b262-0b566e204d05

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
import Theorems.Thm_PairsToBound_widthN_toN
import Theorems.Thm_ClauseBound_Alg_Decode_stDecM
import Theorems.Thm_VariableBound_Rename_encN_toN


set_option autoImplicit false
section
section
open PairsToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg MainTheoremForms VariableBound.Rename
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution : RewritesAtWidthOr3 atWidthOr3 := by
  intro k n φ hk hφ
  obtain ⟨-, hdec⟩ := Decode.stDecM k n φ hk hφ.1
  rw [atWidthOr3, hdec, widthN_toN]
  exact encN_toN _ φ
end PairsToBound
