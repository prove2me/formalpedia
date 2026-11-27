-- Prove2me | solution 1 for P2M_CompanionTheory_WaveGrid_hypLam__13035e3e4a07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:49:37.414716+00:00
-- url     : https://prove2.me/submissions/afdd235d-7a75-496e-9383-b5f08e6c7bce

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Theorems.Thm_P2M_CompanionTheory_WaveGrid_lam__anti_6a5a945442e0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
namespace CompanionTheory.WaveGrid
theorem _root_.solution : HypLam P₂.k P₂.r lam₂ 10 20 41 where
  hc := ⟨lam₂_anti, fun s => ⟨9 - 20 * (s : ℕ), by simp only [lam₂, P₂]; push_cast; ring⟩⟩
  lam_le := by
    intro s
    have hs : (s : ℕ) < 3 := s.2
    have h1 : ((s : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : (s : ℕ) ≤ 2)
    have h0 : (0 : ℝ) ≤ ((s : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [lam₂]
    rw [abs_le]
    constructor <;> linarith
  c_ge := by norm_num
  b_ge_three := by norm_num
  b_ge_k := by
    have := Real.exp_one_lt_d9
    show Real.exp 1 * ((2 : ℕ) : ℝ) ≤ 41
    push_cast
    linarith
  b_ge_c := by norm_num
  g_ge := by norm_num
  gap := by
    intro s t h
    simp only [lam₂, h]
    push_cast
    linarith
end CompanionTheory.WaveGrid
