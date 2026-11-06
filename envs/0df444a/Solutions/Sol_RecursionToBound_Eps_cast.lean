-- Prove2me | solution 1 for RecursionToBound.Eps.cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:22.970198+00:00
-- url     : https://prove2.me/submissions/4a424e87-259a-43ac-a7a6-7fdf3a1e38e7

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

set_option autoImplicit false
section
section
open RecursionToBound
open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
open RecursionToBound.Eps
namespace RecursionToBound.Eps
theorem _root_.solution (r : ℕ × ℕ) : ((epsOf r : ℚ) : ℝ) = min ((r.1 : ℝ) / (r.2 : ℝ)) 1 := by
  rw [epsOf, Rat.cast_min, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, Rat.cast_one]
end RecursionToBound.Eps
