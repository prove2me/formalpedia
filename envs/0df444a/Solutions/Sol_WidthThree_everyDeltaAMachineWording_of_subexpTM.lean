-- Prove2me | solution 1 for WidthThree.everyDeltaAMachineWording_of_subexpTM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:55:48.361114+00:00
-- url     : https://prove2.me/submissions/792e7469-8ecd-4043-a6ec-f0b3cc973273

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

set_option autoImplicit false
section
section
open WidthThree
open Turing
open scoped NNReal
namespace WidthThree
theorem _root_.solution (h : Sat3.SubexpTM) : PaperSentences.ThmEveryDelta := by
  intro δ hδ
  obtain ⟨M, hfin, hM⟩ := h
  obtain ⟨c, hc⟩ := hM ⟨δ, hδ.le⟩ hδ
  exact ⟨c, M, _, hfin, hc, fun n _ => Nat.floor_le (by positivity)⟩
end WidthThree
