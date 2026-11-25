-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_linProj_comp_zeroExt_133519947d4f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:14.75706+00:00
-- url     : https://prove2.me/submissions/895afa1f-239b-410f-a77c-b07e413da8aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadPlaneJac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linProj_zeroExt_b38aab75c095


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
noncomputable section
open Module
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) :
    LinearMap.det ((linProjₗ π).comp (zeroExt m k)) = (coordPlaneBlock π).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin m) ℂ).toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp [linProjₗ, linProj_zeroExt, Matrix.mulVec, dotProduct]
end GroundTheory.Heights₂.Heights
