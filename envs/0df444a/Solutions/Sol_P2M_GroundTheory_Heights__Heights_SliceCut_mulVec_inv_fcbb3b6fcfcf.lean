-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceCut_mulVec_inv_fcbb3b6fcfcf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:18:36.768751+00:00
-- url     : https://prove2.me/submissions/08e2ff1b-767a-4038-bfb7-9079ac1b0413

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut

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
theorem _root_.solution (x : Fin n → ℂ) : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact h.isUnit_det),
    Matrix.one_mulVec]
end GroundTheory.Heights₂.Heights.SliceCut
