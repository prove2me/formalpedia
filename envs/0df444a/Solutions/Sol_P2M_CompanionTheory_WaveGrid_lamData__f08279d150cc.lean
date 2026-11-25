-- Prove2me | solution 1 for P2M_CompanionTheory_WaveGrid_lamData__f08279d150cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:29:12.796218+00:00
-- url     : https://prove2.me/submissions/96ffd6bd-25fa-4757-9329-d10ea903b2a7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_QwBound
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PstMul
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NQText

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset
namespace CompanionTheory.WaveGrid
theorem _root_.solution : LamData P₀ lam₀ 1 2 40 where
  c_pos := by norm_num
  g_ge := by norm_num
  b_ge_three := by norm_num
  b_ge_k := by show ((2 : ℕ) : ℝ) ≤ 40; norm_num
  b_ge_c := by norm_num
  lam_le := by
    intro s _ _
    unfold lam₀
    split_ifs <;> norm_num
  gap := by
    intro s h1 h2
    have : P₀.k = 2 := rfl
    omega
  inter := by
    intro s h1 h2
    have h2' : s ≤ 1 := h2
    interval_cases s
    simp only [lam₀, P₀]
    norm_num
  u_le := by
    intro i h1 h2
    have h2' : i ≤ 2 := h2
    interval_cases i <;> simp [P₀] <;> norm_num
end CompanionTheory.WaveGrid
