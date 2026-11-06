-- Prove2me | solution 1 for PairsToBound.inMainRegime_tests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:15:06.95751+00:00
-- url     : https://prove2.me/submissions/bac40f50-5544-4e39-8339-800287278569

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
import Theorems.Thm_PairsToBound_pow_four_le_lg_iff
import Theorems.Thm_ClauseBound_Alg_Decode_stDecM
import Theorems.Thm_PairsToBound_three_le_widthOr3


set_option autoImplicit false
section
section
open PairsToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg MainTheoremForms VariableBound.Rename
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution (K₀ : ℕ) : TestsTheMainRegime K₀ (inMainRegime K₀) := by
  intro k n φ hk hφ
  obtain ⟨-, hdec⟩ := Decode.stDecM k n φ hk hφ.1
  rw [inMainRegime, hdec, widthN_toN, List.length_replicate, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    pow_four_le_lg_iff (le_trans (by norm_num) (three_le_widthOr3 φ))]
end PairsToBound
