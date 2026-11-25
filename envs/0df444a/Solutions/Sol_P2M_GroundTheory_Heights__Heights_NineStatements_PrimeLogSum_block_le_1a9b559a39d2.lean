-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_block_le_1a9b559a39d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:19.372183+00:00
-- url     : https://prove2.me/submissions/01d6aa5b-5a77-4684-a3a7-bdf8ec479f21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PPrimeLogSum

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
theorem _root_.solution (k : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ Nat.log 2 p = k) :
    ∑ p ∈ S, Real.log p / p ≤ 2 * Real.log 4 := by
  have h1 : ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ S, Real.log p / (2 : ℝ) ^ k := by
    apply sum_le_sum
    intro p hp
    obtain ⟨hpp, hk⟩ := hS p hp
    apply div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity)
    have := Nat.pow_log_le_self 2 hpp.ne_zero
    rw [hk] at this
    exact_mod_cast this
  have h2 : ∑ p ∈ S, Real.log p ≤ Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) := by
    rw [Chebyshev.theta, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpp, hk⟩ := hS p hp
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
      rw [hk] at this
      simp only [mem_filter, mem_Ioc]
      exact ⟨⟨hpp.pos, this.le⟩, hpp⟩
    · intro p _ _
      exact Real.log_natCast_nonneg p
  have h3 := Chebyshev.theta_le_log4_mul_x (x := ((2 ^ (k + 1) : ℕ) : ℝ)) (by positivity)
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  calc ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ S, Real.log p / (2 : ℝ) ^ k := h1
    _ = (∑ p ∈ S, Real.log p) / (2 : ℝ) ^ k := by rw [sum_div]
    _ ≤ Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) / (2 : ℝ) ^ k := by gcongr
    _ ≤ Real.log 4 * ((2 ^ (k + 1) : ℕ) : ℝ) / (2 : ℝ) ^ k := by gcongr
    _ = 2 * Real.log 4 := by
      push_cast
      rw [pow_succ]
      field_simp
end GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
