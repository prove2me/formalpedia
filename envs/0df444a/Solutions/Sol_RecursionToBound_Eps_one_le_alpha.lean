-- Prove2me | solution 1 for RecursionToBound.Eps.one_le_alpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:55.141716+00:00
-- url     : https://prove2.me/submissions/30ae1388-90e3-4082-8638-3961aca2fd4a

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
import Theorems.Thm_RecursionToBound_Eps_pos
import Theorems.Thm_RecursionToBound_Eps_le_one
import Theorems.Thm_SparsificationLemma_StepSparsify_one_le_alpha


set_option autoImplicit false
section
section
open RecursionToBound
open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
open RecursionToBound.Eps
namespace RecursionToBound.Eps
theorem _root_.solution {k : ℕ} {r : ℕ × ℕ} (hk : 3 ≤ k) (h1 : 0 < r.1) (h2 : 0 < r.2) : 1 ≤ Cal.alphaC k (epsOf r) :=
  SparsificationLemma.StepSparsify.one_le_alpha hk (pos h1 h2) (le_one r)
end RecursionToBound.Eps
