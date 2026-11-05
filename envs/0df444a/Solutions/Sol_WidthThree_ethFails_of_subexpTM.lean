-- Prove2me | solution 1 for WidthThree.ethFails_of_subexpTM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:55:39.591924+00:00
-- url     : https://prove2.me/submissions/f634897a-c157-4f8a-a277-fc192b3fd2ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_ThmEveryDeltaStatement
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_ToTuring_EndLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_WidthThree_Rates
import Theorems.Thm_Sat3_SubexpTM_not_ETH_TM


set_option autoImplicit false
section
section
open WidthThree
open Turing
open scoped NNReal
namespace WidthThree
theorem _root_.solution (h : Sat3.SubexpTM) : ¬ Sat3.ETH_TM := h.not_ETH_TM
end WidthThree
