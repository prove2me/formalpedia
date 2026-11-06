-- Prove2me | solution 1 for PairsToBound.thmVariablesAImpliesThmVariablesB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:26:14.019206+00:00
-- url     : https://prove2.me/submissions/5f6b7951-bdab-4bfd-bfd8-6eae0ec36baf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_PairsToBound_Pairs
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_PairsToBound_Width
import Definitions.Def_PairsToBound_FrontEnd
import Definitions.Def_PairsToBound_Exhaust
import Definitions.Def_TwoMachines_Main
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_PairsToBound_Main
import Theorems.Thm_PairsToBound_thmVariablesBFromThmVariablesA
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_GeneralPieces_x_Of_ge_2a558e3f9765
import Theorems.Thm_PairsToBound_thePairsSatisfyTheHypothesis
import Theorems.Thm_PairsToBound_thetaOfThePairs


set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution : ThmVariablesAImpliesThmVariablesB := by
  intro hVariablesA hB
  obtain ⟨c, P, A, val, hP, -⟩ := hB
  obtain ⟨C₀, Cp, h⟩ := thePairsSatisfyTheHypothesis c
  obtain ⟨Q, hpoly, hK, -, -, hprec⟩ := h P A val hP
  obtain ⟨M, C', hfin, hM⟩ := hVariablesA _ _ _ C₀ Q hpoly RecursionWithPieces.prec Cp hprec
  have he : ∀ l : ℕ, Levels.Gen.e (1 / Real.sqrt 2) (GeneralPieces.x₀Of c) l ≤ ((3 * GeneralPieces.x₀Of c + 6 : ℕ) : ℝ) / Real.sqrt (lg ((RecursionWithPieces.solverAB P val c).K (Q.idx l))) := fun l => by
    rw [hK]
    obtain ⟨-, -, -, -, -, h6⟩ := thetaOfThePairs (GeneralPieces.x₀Of c) l (GeneralPieces.x₀Of_ge c)
    refine h6.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    have hx : (0 : ℝ) ≤ (GeneralPieces.x₀Of c : ℝ) := Nat.cast_nonneg _
    have hs : Real.sqrt (3 * (GeneralPieces.x₀Of c : ℝ) + 6) ≤ 3 * (GeneralPieces.x₀Of c : ℝ) + 6 := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hs0 := Real.sqrt_nonneg (3 * (GeneralPieces.x₀Of c : ℝ) + 6)
    push_cast
    linarith
  obtain ⟨⟨Mb, c', qb, pre, test, K₁, K₂, N, q₀, q, -, hMb, -, -, hpre, -, htest, hfN, -, hCh⟩, hall⟩ := thmVariablesBFromThmVariablesA _ _ _ C₀ Q _ he M C' hfin hM
  obtain ⟨C, hC⟩ := hall Mb c' hMb pre test hpre htest N q hCh
  exact ⟨N, C, hfN, hC⟩
end PairsToBound
