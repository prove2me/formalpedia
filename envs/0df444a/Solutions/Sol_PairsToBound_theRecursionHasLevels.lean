-- Prove2me | solution 1 for PairsToBound.theRecursionHasLevels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:57:37.670666+00:00
-- url     : https://prove2.me/submissions/6dc67f52-5b55-4fb8-975b-baa5cb397154

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Rec_PartB
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_PairsToBound_Pairs
import Theorems.Thm_PairsToBound_seq_of_rate
import Theorems.Thm_ClauseBound_Alg_Need_stNeedG
import Theorems.Thm_CountKSat_ProgC_pick_spec
import Theorems.Thm_GeneralPieces_Chain_stChain2
import Theorems.Thm_GeneralPieces_K_idx
import Theorems.Thm_GeneralPieces_par_of_isPieces
import Theorems.Thm_GeneralPieces_pick_spec
import Theorems.Thm_GeneralPieces_solveG2
import Theorems.Thm_GeneralPieces_solver_poly
import Theorems.Thm_GeneralPieces_stRate2
import Theorems.Thm_PaddedDescent_F_Price_rho_lt


set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen GeneralPieces MainTheoremForms
namespace PairsToBound
theorem _root_.solution : TheRecursionHasLevels := by
  intro c
  obtain ⟨C₀, hC⟩ := seq_of_rate Chain.stChain2 stRate2 solveG2 Need.stNeedG c
  refine ⟨C₀, fun ρ x₀ P A val h hx hx2 => ?_⟩
  obtain ⟨hP, hKeeps, hm⟩ := par_of_isPieces h
  obtain ⟨hp1, hp2, hp3, hp4⟩ := pick_spec (Tied.recOf P val c) x₀
  obtain ⟨Q, hQ, hpick⟩ := hC (Tied.recOf P val c) ρ x₀ h.rho_ge h.rho_lt hP hm hx hx2 _ hp1 hp2 hp3 hp4
  exact ⟨Q, solver_poly _ hKeeps, fun l => by rw [hQ, K_idx], hpick⟩
end PairsToBound
