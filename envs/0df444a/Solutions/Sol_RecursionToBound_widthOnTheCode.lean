-- Prove2me | solution 1 for RecursionToBound.widthOnTheCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:02:05.772746+00:00
-- url     : https://prove2.me/submissions/dd68af01-e140-4a27-a8f8-05c0ac37ec6f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Cal_Facts
import Definitions.Def_StepSparsify_CalLeaves
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Main
import Definitions.Def_ClauseBound_Alg_Decode
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_RecursionToBound_Tree
import Theorems.Thm_RecursionToBound_widthOr3F_toN
import Theorems.Thm_ClauseBound_Alg_Decode_stDecM
import Theorems.Thm_VariableBound_VariablesA_level_eq_pick
import Theorems.Thm_VariableBound_VariablesA_pick_eq


set_option autoImplicit false
section
section
open RecursionToBound
open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
namespace RecursionToBound
theorem _root_.solution : WidthOnTheCode := by
  refine ⟨fun k n φ hk hφ => ?_, fun Idx _ S e C₀ Q num k n l φ hk hφ hl => ?_⟩
  · obtain ⟨-, hdec⟩ := Decode.stDecM k n φ hk hφ.1
    rw [widthU, hdec]
    exact widthOr3F_toN φ
  · obtain ⟨-, hdec⟩ := Decode.stDecM k n φ hk hφ.1
    have hn : nU (SatM.enc k φ) = n := by rw [nU, hdec, List.length_replicate]
    have hi : idxU Q.pick (SatM.enc k φ) = Q.idx l := by rw [idxU, hn, Q.pick_idx, VariableBound.VariablesA.level_eq_pick Q hl]
    exact ⟨by rw [numU, hi, hn, VariableBound.VariablesA.pick_eq Q hl], hi⟩
end RecursionToBound
