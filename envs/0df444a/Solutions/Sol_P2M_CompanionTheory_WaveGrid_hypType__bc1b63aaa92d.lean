-- Prove2me | solution 1 for P2M_CompanionTheory_WaveGrid_hypType__bc1b63aaa92d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:12:21.717805+00:00
-- url     : https://prove2.me/submissions/99ce51a6-a70f-42a9-9be3-575001c2c65e

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
theorem _root_.solution (a : ℤ) (ha : 10 ≤ a) (ha' : a ≤ 40) :
    HypType P₂.k P₂.r lam₂ (fun i => if i = 1 then (a : ℝ) + 1 / 2 else 1 / 2) 41 where
  half := by
    intro i _ _
    by_cases h : i = 1
    · exact ⟨a, by simp [h, P₂]; norm_num⟩
    · exact ⟨0, by simp [h, P₂]; norm_num⟩
  inter := by
    have haR : (10 : ℝ) ≤ a := by exact_mod_cast ha
    refine ⟨fun s t hst => lam₂_anti (by simpa using hst), fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
    · have hs' : (s : ℕ) + 1 ≤ 2 := hs
      simp only [lam₂, Fin.val_cast]
      split_ifs with h
      · have : (s : ℕ) = 0 := by omega
        rw [this]; push_cast; linarith
      · have : (s : ℕ) = 1 := by omega
        rw [this]; norm_num
    · have hs' : (s : ℕ) + 2 ≤ 2 := hs
      have : (s : ℕ) = 0 := by omega
      simp only [lam₂, Fin.val_cast, this]
      norm_num
  u_le := by
    intro i _ _
    have haR : (10 : ℝ) ≤ a := by exact_mod_cast ha
    have haR' : (a : ℝ) ≤ 40 := by exact_mod_cast ha'
    rw [abs_le]
    split_ifs <;> constructor <;> linarith
end CompanionTheory.WaveGrid
