-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ofReal_mul_poincareDeepWeight_le_a0152c518374
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:35:21.767824+00:00
-- url     : https://prove2.me/submissions/2acf9468-130d-4f67-ad0e-3c3e8b0a6f6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepWeightMass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (r : ℝ) :
    ENNReal.ofReal r * ENNReal.ofReal (if Real.log (|r| ^ 2) < -Real.exp 1 then
        (|r| ^ 2 * Real.log (|r| ^ 2) ^ 2)⁻¹ else 0) ≤
      (Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2)))).indicator
        (fun r : ℝ => ENNReal.ofReal (((Real.log r) ^ 2 * r)⁻¹ / 4)) r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ENNReal.ofReal_of_nonpos hr]
  · rw [abs_of_pos hr]
    split_ifs with hc
    · have hl : Real.log (r ^ 2) = 2 * Real.log r := by rw [Real.log_pow]; norm_num
      rw [hl] at hc
      have hlr : Real.log r < -(Real.exp 1 / 2) := by linarith
      have hl0 : Real.log r ≠ 0 := (hlr.trans (by have := Real.exp_pos 1; linarith)).ne
      rw [Set.indicator_of_mem (show r ∈ Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2))) from ⟨hr, ((Real.log_lt_iff_lt_exp hr).1 hlr).le⟩), ← ENNReal.ofReal_mul hr.le, hl]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      field_simp
      ring
    · simp
end GroundTheory.Heights₂.Heights
