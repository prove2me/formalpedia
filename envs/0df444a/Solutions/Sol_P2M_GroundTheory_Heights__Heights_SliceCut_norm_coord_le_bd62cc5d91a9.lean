-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceCut_norm_coord_le_bd62cc5d91a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:15:52.528864+00:00
-- url     : https://prove2.me/submissions/9cff6b4c-fb5c-4d60-ac78-6a0166a78c87

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
theorem _root_.solution (x : Fin n → ℂ) (i : Fin n) : ‖((h.matᵀ)⁻¹ *ᵥ x) i‖ ≤ h.dualNorm x := by
  unfold HermNorm.dualNorm
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => ‖((h.matᵀ)⁻¹ *ᵥ x) j‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ i)
end GroundTheory.Heights₂.Heights.SliceCut
