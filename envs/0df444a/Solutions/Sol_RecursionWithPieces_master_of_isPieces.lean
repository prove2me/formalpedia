-- Prove2me | solution 1 for RecursionWithPieces.master_of_isPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:13:19.066239+00:00
-- url     : https://prove2.me/submissions/4ab054af-78f4-429c-9aa5-075441de39ba

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
import Theorems.Thm_RecursionWithPieces_master_of_par
import Theorems.Thm_GeneralPieces_par_of_isPieces
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_P2M_GeneralPieces_x_Of_ge_2a558e3f9765
import Theorems.Thm_P2M_GeneralPieces_x_Of_pow_e8c07e605600
import Theorems.Thm_PaddedDescent_F_Price_rho_lt
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open RecursionWithPieces
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks ClauseBound.Both UniformInK VariableBound GeneralPieces
namespace RecursionWithPieces
theorem _root_.solution {R : ∀ (Idx : Type) [Enc Idx], Solver Idx → (U → U × Idx) → (U → U) → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (hEnd : StEndS R) {ρ : ℝ} {c : ℕ} {P₀ : PiecesF}
    {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} (h : AppRunningTime.IsPieces ρ c P₀ A val) :
    R _ (solverOf (Tied.recOf P₀ val c)) (Pick.pick (Tied.recOf P₀ val c) (x₀Of c)) (fun u => () :: u) (SatK.rN 1 (AppRunningTime.alpha' ρ)) (SatM.rPow (AppRunningTime.alpha' ρ)) := by
  obtain ⟨hP, hKeeps, hm⟩ := par_of_isPieces h
  exact master_of_par hEnd h.rho_ge h.rho_lt hP hm hKeeps (x₀Of_ge c) (x₀Of_pow c)
end RecursionWithPieces
