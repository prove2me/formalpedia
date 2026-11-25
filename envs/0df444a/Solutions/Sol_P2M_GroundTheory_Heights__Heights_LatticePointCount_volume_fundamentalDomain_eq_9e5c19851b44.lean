-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticePointCount_volume_fundamentalDomain_eq_9e5c19851b44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:30.028196+00:00
-- url     : https://prove2.me/submissions/35570e02-227e-49c3-acc4-cc79a7a42fc0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VolumeFundamentalDomainEq

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
open MeasureTheory Metric Module Submodule
open scoped ENNReal Pointwise
open GroundTheory.Heights₂.Heights.LatticePointCount
namespace GroundTheory.Heights₂.Heights.LatticePointCount
theorem _root_.solution {r : ℕ} (c : Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) :
    volume (ZSpan.fundamentalDomain c) =
      ENNReal.ofReal |(EuclideanSpace.basisFun (Fin r) ℝ).toBasis.det c| := by
  rw [ZSpan.measure_fundamentalDomain c volume (EuclideanSpace.basisFun (Fin r) ℝ).toBasis,
    measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume)]
  rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped, mul_one]
end GroundTheory.Heights₂.Heights.LatticePointCount
