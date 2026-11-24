-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_mulMat_sum_04dda0bf4bd3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:47.721476+00:00
-- url     : https://prove2.me/submissions/866f245b-2c13-47c6-af1d-34b9b7cb9302

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOnPlane

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
theorem _root_.solution (α : 𝓞 K) (m : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    ∑ n, (mulMat α m n : K) * integralBasis K n = (α : K) * integralBasis K m := by
  have h := congrArg (algebraMap (𝓞 K) K) ((RingOfIntegers.basis K).sum_repr
    (α * RingOfIntegers.basis K m))
  simp only [map_sum, map_mul, zsmul_eq_mul, map_intCast] at h
  simpa only [integralBasis_apply, mulMat, RingOfIntegers.coe_eq_algebraMap] using h
end GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
