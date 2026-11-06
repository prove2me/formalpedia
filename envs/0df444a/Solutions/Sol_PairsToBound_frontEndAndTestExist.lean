-- Prove2me | solution 1 for PairsToBound.frontEndAndTestExist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:25:22.346416+00:00
-- url     : https://prove2.me/submissions/832b7fcb-2d2c-4c6a-90d2-6ac3d8928fd9

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
import Theorems.Thm_PairsToBound_atWidthOr3_rewrites
import Theorems.Thm_PairsToBound_inMainRegime_tests
import Theorems.Thm_PairsToBound_atWidthOr3_polyT
import Theorems.Thm_PairsToBound_inMainRegime_polyT

set_option autoImplicit false
section
section
open PairsToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg MainTheoremForms VariableBound.Rename
open Sat3 (CNF)
variable {α : Type} [Enc α]
namespace PairsToBound
theorem _root_.solution : FrontEndAndTestExist :=
  ⟨⟨atWidthOr3, atWidthOr3_polyT, atWidthOr3_rewrites⟩, fun K₀ => ⟨inMainRegime K₀, inMainRegime_polyT K₀, inMainRegime_tests K₀⟩⟩
end PairsToBound
