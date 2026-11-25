-- Prove2me | solution 1 for P2M_CompanionTheory_WaveGrid_movedData__c0af71514bc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:34.29013+00:00
-- url     : https://prove2.me/submissions/707333a8-78e6-4a09-9231-a2549b2ec4bb

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
theorem _root_.solution : MovedData P₁ 2 lam₀ 1 2 40 where
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
    have : P₁.k = 2 := rfl
    omega
  inter := by
    intro s h1 h2
    have h2' : s ≤ 1 := h2
    interval_cases s
    simp only [lam₀, P₁]
    norm_num
  moved := by
    intro i hi
    simp only [P₁]
    split_ifs <;> simp_all
  ul_le := by
    simp only [P₁]
    norm_num
end CompanionTheory.WaveGrid
