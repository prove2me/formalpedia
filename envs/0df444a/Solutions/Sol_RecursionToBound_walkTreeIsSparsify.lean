-- Prove2me | solution 1 for RecursionToBound.walkTreeIsSparsify
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:47:34.367747+00:00
-- url     : https://prove2.me/submissions/2b718894-60ee-402f-8007-501b98bb2a54

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
import Theorems.Thm_SparsificationLemma_Cal_factI
import Theorems.Thm_SparsificationLemma_StepSparsify_one_le_alpha
import Theorems.Thm_SparsificationLemma_stNoTaut
import Theorems.Thm_SparsificationLemma_stOutputsSame
import Theorems.Thm_StepSparsify_leaves_eq_of_le


set_option autoImplicit false
section
section
open RecursionToBound
open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
namespace RecursionToBound
theorem _root_.solution : WalkTreeIsSparsify := by
  intro k n D r ψ hk h1 h2 hψ hD
  have hα := Eps.one_le_alpha hk h1 h2
  have hψ' : IsKCNF k n (noTaut ψ) := (stNoTaut ψ).2.1 k n hψ
  have e : tree (Cal.thetaC (Cal.alphaC k (epsOf r))) k D (noTaut ψ) = tree (Cal.thetaC (Cal.alphaC k (epsOf r))) k (Cal.depthC (Cal.alphaC k (epsOf r)) k n) (noTaut ψ) :=
    _root_.StepSparsify.leaves_eq_of_le _ _ D _ hD (Cal.factI (Cal.alphaC k (epsOf r)) k n (noTaut ψ) hα (by omega) hψ')
  unfold thresholds
  rw [stOutputsSame, outputs, e]
  rfl
end RecursionToBound
