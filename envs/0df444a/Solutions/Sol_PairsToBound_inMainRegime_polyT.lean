-- Prove2me | solution 1 for PairsToBound.inMainRegime_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:14:10.904956+00:00
-- url     : https://prove2.me/submissions/ca0ae356-6871-4ede-bedf-fb5b6f4b5a11

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
import Theorems.Thm_PairsToBound_both_le_polyT
import Theorems.Thm_ClauseBound_Alg_Decode_stCertDecM
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_two_pow
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.snd



set_option autoImplicit false
section
section
open PairsToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg MainTheoremForms VariableBound.Rename
open Sat3 (CNF)
variable {α : Type} [Enc α]
namespace PairsToBound
theorem _root_.solution (K₀ : ℕ) : PolyT (inMainRegime K₀) := by
  have hd : PolyT fmlOf := Decode.stCertDecM.2
  have hw : Unary fun x => widthN (fmlOf x).2 := widthN_unary hd.snd
  have h4 : Unary fun x => widthN (fmlOf x).2 ^ 4 := by
    have h := ((hw.mul hw).mul hw).mul hw
    unfold Unary at h ⊢
    exact h.congr fun x => by congr 1; ring
  have h2 : PolyT fun x => 2 ^ (widthN (fmlOf x).2 ^ 4) := PolyT.two_pow h4
  have hn : PolyT fun x => (fmlOf x).1.length := PolyT.length hd.fst
  exact both_le_polyT (PolyT.const _) h2 hn
end PairsToBound
