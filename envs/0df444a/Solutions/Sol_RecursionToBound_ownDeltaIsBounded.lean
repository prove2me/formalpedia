-- Prove2me | solution 1 for RecursionToBound.ownDeltaIsBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:40:05.578062+00:00
-- url     : https://prove2.me/submissions/1ff82cb3-d0a1-4af7-bda5-c549f779367b

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
import Theorems.Thm_RecursionToBound_Eps_one_le_alpha
import Theorems.Thm_SparsificationLemma_Cal_gen
import Theorems.Thm_SparsificationLemma_StepSparsify_one_le_alpha
import Theorems.Thm_SparsificationLemma_stNoTaut


set_option autoImplicit false
section
section
open RecursionToBound
open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
namespace RecursionToBound
theorem _root_.solution : OwnDeltaIsBounded := by
  intro k n r ψ hk h1 h2 hψ Φ hΦ
  have hα := Eps.one_le_alpha hk h1 h2
  have hψ' : IsKCNF k n (noTaut ψ) := (stNoTaut ψ).2.1 k n hψ
  have h : ∀ v, occN Φ v ≤ occBound k r := ((Cal.gen hα (by omega) hψ').2.2.1 Φ hΦ).2
  have h2 : 2 ≤ occBound k r := by
    unfold occBound
    omega
  exact max_le h2 (Finset.sup_le fun v _ => h v)
end RecursionToBound
