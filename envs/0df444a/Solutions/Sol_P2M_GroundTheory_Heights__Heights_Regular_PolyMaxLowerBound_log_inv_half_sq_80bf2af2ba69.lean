-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_log_inv_half_sq_80bf2af2ba69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:26.597694+00:00
-- url     : https://prove2.me/submissions/53496e0c-15f8-40e5-8e50-0d356fd17286

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PPolyMaxLowerBound

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
open Metric Set
open ReciprocityTheory.AnForm.A (polyMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace PolyMaxLowerBound
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    Real.log ((t / 2) ^ 2)⁻¹ = 2 * Real.log 2 + 2 * Real.log t⁻¹ := by
  have h : ((t / 2) ^ 2)⁻¹ = (2 * t⁻¹) ^ 2 := by field_simp
  rw [h, Real.log_pow, Real.log_mul (by norm_num) (inv_ne_zero ht.ne')]
  push_cast; ring
end PolyMaxLowerBound
end GroundTheory.Heights₂.Heights.Regular
