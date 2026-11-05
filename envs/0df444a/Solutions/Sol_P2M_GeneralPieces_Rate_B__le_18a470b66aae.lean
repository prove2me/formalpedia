-- Prove2me | solution 1 for P2M_GeneralPieces_Rate_B__le_18a470b66aae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:42.609628+00:00
-- url     : https://prove2.me/submissions/9db4d706-06bf-4fdc-aaf8-b0cd56c83e5b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_GeneralPieces_Rate_B_aux
import Theorems.Thm_ClauseBound_Gen_Rate_K_le_g
import Theorems.Thm_ClauseBound_Gen_Rate_bNext_eq
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    bNextG P (step P x₀ l) lam B ≤ g x₀ l ^ 4 * lam + g x₀ l ^ 2 * (g x₀ l * B + g x₀ l ^ 2 * (2 * lam) ^ c) := by
  rw [bNext_eq, hm]
  have hK := big_le_K hx l
  have hg := K_le_g x₀ l
  refine (B_aux (K x₀ l) (g x₀ l) _ lam _ (by omega) (by omega) (Nat.div_mul_le_self _ _)).trans ?_
  have := hP.bits 0 lam hlam
  gcongr
end GeneralPieces.Rate
