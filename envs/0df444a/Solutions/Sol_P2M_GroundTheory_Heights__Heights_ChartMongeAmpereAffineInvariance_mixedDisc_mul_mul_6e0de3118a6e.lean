-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mixedDisc_mul_mul_6e0de3118a6e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:07.365179+00:00
-- url     : https://prove2.me/submissions/719b850a-c6a8-4978-b301-b1c6ab57e7dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
theorem _root_.solution (P Q : Matrix (Fin D) (Fin D) ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => P * A k * Q) = P.det * Q.det * mixedDisc A := by
  have hS : ∀ S : Finset (Fin D), (∑ k ∈ S, P * A k * Q) = P * (∑ k ∈ S, A k) * Q := fun S => by
    rw [Finset.mul_sum, Finset.sum_mul]
  simp only [mixedDisc, hS, det_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  ring
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
