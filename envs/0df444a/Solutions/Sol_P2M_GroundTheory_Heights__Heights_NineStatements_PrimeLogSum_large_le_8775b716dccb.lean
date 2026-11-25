-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_large_le_8775b716dccb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:42.581806+00:00
-- url     : https://prove2.me/submissions/3050a0f6-fbd2-4c42-9502-43f46b8b59af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PPrimeLogSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_term_le_cb387f1df1fe

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
theorem _root_.solution {B : ℕ} (hB : 2 ≤ B) (S : Finset ℕ) (hS : ∀ p ∈ S, B < p) (hcard : S.card ≤ B) :
    ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log B := by
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have he : Real.exp 1 ≤ (B : ℝ) + 1 := by
    have := Real.exp_one_lt_d9
    linarith
  have hterm : ∀ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)) := by
    intro p hp
    have hBp : B + 1 ≤ p := hS p hp
    have hBp' : (B : ℝ) + 1 ≤ p := by exact_mod_cast hBp
    refine (term_le (by omega)).trans ?_
    have := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he)
      (Set.mem_Ici.mpr (he.trans hBp')) hBp'
    simp only at this
    linarith
  have hsum := sum_le_sum hterm
  rw [sum_const, nsmul_eq_mul] at hsum
  have hcard' : (S.card : ℝ) ≤ B := by exact_mod_cast hcard
  have hlogpos : 0 ≤ Real.log ((B : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hq : 0 ≤ 2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)) := by positivity
  have h1 : (S.card : ℝ) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)))
      ≤ 2 * Real.log ((B : ℝ) + 1) := by
    calc (S.card : ℝ) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)))
        ≤ ((B : ℝ) + 1) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1))) := by
          gcongr
          linarith
      _ = 2 * Real.log ((B : ℝ) + 1) := by field_simp
  have h2 : Real.log ((B : ℝ) + 1) ≤ 2 * Real.log B := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < (B : ℝ) + 1)
      (show (B : ℝ) + 1 ≤ (B : ℝ) ^ 2 by nlinarith)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  linarith
end GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
