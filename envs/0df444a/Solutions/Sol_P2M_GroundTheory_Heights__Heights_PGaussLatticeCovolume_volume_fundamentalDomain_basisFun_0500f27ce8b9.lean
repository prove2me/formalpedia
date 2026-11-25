-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_volume_fundamentalDomain_basisFun_0500f27ce8b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:46.294977+00:00
-- url     : https://prove2.me/submissions/9da486c0-5512-4860-8029-5aedd795e772

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeCovolume

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
open Matrix MeasureTheory Module
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussLatticeCovolume
namespace GroundTheory.Heights₂.Heights.PGaussLatticeCovolume
theorem _root_.solution (g : ℕ) :
    volume.real (ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin g) ℝ).toBasis) = 1 := by
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume),
    OrthonormalBasis.coe_toBasis, measureReal_def,
    (EuclideanSpace.basisFun (Fin g) ℝ).volume_parallelepiped, ENNReal.toReal_one]
end GroundTheory.Heights₂.Heights.PGaussLatticeCovolume
