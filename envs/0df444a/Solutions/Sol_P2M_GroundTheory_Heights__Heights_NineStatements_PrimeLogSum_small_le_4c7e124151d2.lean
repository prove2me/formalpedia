-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_small_le_4c7e124151d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:10.677977+00:00
-- url     : https://prove2.me/submissions/79f6ccc7-2032-493b-814f-796d74ce5355

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PPrimeLogSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_block_le_1a9b559a39d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_natLog_mul_log_two_le_171220f6ad14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open Finset
open GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
namespace GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
theorem _root_.solution {N : ℕ} (hN : 2 ≤ N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N) :
    ∑ p ∈ S, Real.log p / p ≤ 8 * Real.log N := by
  have hmap : ∀ p ∈ S, Nat.log 2 p ∈ range (Nat.log 2 N + 1) := by
    intro p hp
    simp only [mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (hS p hp).2)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hblocks : ∑ k ∈ range (Nat.log 2 N + 1), ∑ p ∈ S with Nat.log 2 p = k, Real.log p / p
      ≤ ∑ k ∈ range (Nat.log 2 N + 1), 2 * Real.log 4 := by
    apply sum_le_sum
    intro k _
    apply block_le k
    intro p hp
    simp only [mem_filter] at hp
    exact ⟨(hS p hp.1).1, hp.2⟩
  have hcount : ∑ k ∈ range (Nat.log 2 N + 1), 2 * Real.log 4
      = 2 * Real.log 4 * ((Nat.log 2 N : ℝ) + 1) := by
    simp [sum_const, card_range]
    ring
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN'
  have hnl := natLog_mul_log_two_le (N := N) (by omega)
  have hl2pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc _ ≤ _ := hblocks
    _ = 2 * Real.log 4 * ((Nat.log 2 N : ℝ) + 1) := hcount
    _ = 4 * ((Nat.log 2 N : ℝ) * Real.log 2 + Real.log 2) := by rw [hlog4]; ring
    _ ≤ 4 * (Real.log N + Real.log N) := by gcongr
    _ ≤ 8 * Real.log N := by linarith
end GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
