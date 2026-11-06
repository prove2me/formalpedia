-- Prove2me | solution 1 for RecursionWithPieces.master_of_isPiecesB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:22:46.632229+00:00
-- url     : https://prove2.me/submissions/c5878370-040c-4d36-891e-4a7d892695c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionWithPieces_Defs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_UniformInK_Top_FallBack
import Definitions.Def_ClauseBound_MainBoth
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_RecursionWithPieces_Master
import Theorems.Thm_RecursionWithPieces_master_of_isPieces
import Theorems.Thm_GeneralPieces_Asymptotic_alpha_half
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open RecursionWithPieces
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks ClauseBound.Both UniformInK VariableBound GeneralPieces
namespace RecursionWithPieces
theorem _root_.solution {R : ∀ (Idx : Type) [Enc Idx], Solver Idx → (U → U × Idx) → (U → U) → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (hEnd : StEndS R) {c : ℕ} {P₀ : PiecesF}
    {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} (h : Tied.IsPiecesB c P₀ A val) :
    R _ (solverAB P₀ val c) (pickAB P₀ val c) prec (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) := by
  have h1 := master_of_isPieces hEnd h.1
  rw [AppRunningTime.alpha', Asymptotic.alpha_half] at h1
  exact h1
end RecursionWithPieces
