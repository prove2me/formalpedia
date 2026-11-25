-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_det_cols_ee6747bf1c9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:44.545433+00:00
-- url     : https://prove2.me/submissions/89f24f47-83e7-4718-88d7-b3b0e75f760b

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
theorem _root_.solution {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) :
    (EuclideanSpace.basisFun (Fin g) ℝ).toBasis.det (cols B) = B.det := by
  rw [Basis.det_apply]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, cols]
end GroundTheory.Heights₂.Heights.PGaussLatticeCovolume
