-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_expCover_mem_ball_a7e28df76d18
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:57.206099+00:00
-- url     : https://prove2.me/submissions/254f3f62-ab13-4ec7-b0db-68d8e2a92bdf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    expCover a w ∈ ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro k
  by_cases hk : k.val < a
  · have hre := hw.1 ⟨k.val, hk⟩
    have hkk : Fin.castLE h ⟨k.val, hk⟩ = k := Fin.ext rfl
    rw [hkk] at hre
    simp only [expCover, hk, if_true, Complex.norm_exp]
    simpa using Real.exp_lt_exp.mpr hre
  · simp only [expCover, hk, if_false]
    exact hw.2 k (not_lt.1 hk)
end GroundTheory.Heights₂.Heights.Regular
