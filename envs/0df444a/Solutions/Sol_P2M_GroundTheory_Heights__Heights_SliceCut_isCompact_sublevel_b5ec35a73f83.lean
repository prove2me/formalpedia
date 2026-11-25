-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceCut_isCompact_sublevel_b5ec35a73f83
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:25:31.167507+00:00
-- url     : https://prove2.me/submissions/d683c743-109d-4d81-bf43-f8b3cb051d7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_continuous_dualNorm_d0655469d688
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_norm_coord_le_bd62cc5d91a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_mulVec_inv_fcbb3b6fcfcf

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
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.SliceCut
variable {n : ℕ} (h : HermNorm n)
namespace GroundTheory.Heights₂.Heights.SliceCut
theorem _root_.solution (R : ℝ) : IsCompact {x : Fin n → ℂ | h.dualNorm x ≤ R} := by
  refine ((isCompact_closedBall (0 : Fin n → ℂ) R).image
    (Continuous.matrix_mulVec (A := fun _ => h.matᵀ) continuous_const continuous_id)).of_isClosed_subset
    (isClosed_le (continuous_dualNorm h) continuous_const) fun x hx => ?_
  refine ⟨(h.matᵀ)⁻¹ *ᵥ x, ?_, mulVec_inv h x⟩
  have hR : 0 ≤ R := (Real.sqrt_nonneg _).trans hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  exact fun i => (norm_coord_le h x i).trans hx
end GroundTheory.Heights₂.Heights.SliceCut
