-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussLatticeCovolume_proof_77619a5f89f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:57.042463+00:00
-- url     : https://prove2.me/submissions/c1e19071-5637-4ae7-bfd8-2baf1f55b2e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_coe_intBasis_a5954385bb74
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_det_cols_ee6747bf1c9a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_volume_fundamentalDomain_basisFun_0500f27ce8b9

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
open PGaussLatticeCovolume
namespace GroundTheory.Heights₂.Heights
namespace GaussLatticeCovolume
theorem _root_.solution (hL : GaussLatticeIsLattice.Statement) :
    GaussLatticeCovolume.Statement := by
  intro g B hB
  have : DiscreteTopology (gaussLattice B) := (hL g B hB).1
  have : IsZLattice ℝ (gaussLattice B) := (hL g B hB).2
  rw [ZLattice.covolume_eq_det_mul_measureReal (gaussLattice B) volume (intBasis hB)
      (EuclideanSpace.basisFun (Fin g) ℝ).toBasis,
    coe_intBasis, det_cols, volume_fundamentalDomain_basisFun, mul_one]
end GaussLatticeCovolume
end GroundTheory.Heights₂.Heights
