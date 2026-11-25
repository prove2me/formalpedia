-- Prove2me | solution 1 for P2M_CompanionTheory_WaveGrid_P__OK_75fc07c09722
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:29.785324+00:00
-- url     : https://prove2.me/submissions/f6145691-e65e-4152-9320-9f7ecb569ca3

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NQText
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample

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
theorem _root_.solution : P₁.OK where
  k_pos := by show 1 ≤ 2; norm_num
  T_pos := by show (0 : ℝ) < 1; norm_num
  T'_pos := by show (0 : ℝ) < 1; norm_num
  int_u := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
    have h2' : i ≤ 2 := h2
    interval_cases i
    · exact ⟨0, by simp [P₁]⟩
    · exact ⟨-40, by simp [P₁]⟩
  int_u' := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
    have h2' : i ≤ 2 := h2
    interval_cases i
    · exact ⟨0, by simp [P₁]⟩
    · exact ⟨-4, by simp [P₁]; norm_num⟩
  gap := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
    have h2' : i ≤ 1 := h2
    interval_cases i
    simp only [M.Par.lo, M.Par.hi, P₁]
    norm_num
end CompanionTheory.WaveGrid
