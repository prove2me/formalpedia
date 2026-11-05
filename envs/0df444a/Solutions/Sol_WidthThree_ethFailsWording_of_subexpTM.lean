-- Prove2me | solution 1 for WidthThree.ethFailsWording_of_subexpTM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:56:30.636376+00:00
-- url     : https://prove2.me/submissions/c7f80ee3-b258-4a79-a18d-15836b7c0dee

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
theorem _root_.solution (h : Sat3.SubexpTM) : ¬ PaperSentences.ETH := fun hE => h.not_ETH_TM (hE 3 le_rfl)
end WidthThree
