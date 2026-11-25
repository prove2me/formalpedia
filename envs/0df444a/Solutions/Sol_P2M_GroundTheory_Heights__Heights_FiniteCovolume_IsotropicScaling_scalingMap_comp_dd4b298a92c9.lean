-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_comp_dd4b298a92c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:08:34.103797+00:00
-- url     : https://prove2.me/submissions/08b1f238-14f1-40f6-8225-248cb85f021e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIsotropicScaling
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_apply_eff752ab2046
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_pairing_left_0dea550bfb9e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_pairing_right_8c8b388a4a3d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable (h : HermitianForm F E W) {v w : W}
variable (hvv : h.toSesq v v = 0) (hww : h.toSesq w w = 0) (hvw : h.toSesq v w = 1)
  (hwv : h.toSesq w v = 1)
include hvv hww hvw hwv
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
theorem _root_.solution (α β α' β' : E) :
    scalingMap h v w α β ∘ₗ scalingMap h v w α' β' =
      scalingMap h v w (α + α' + α * α') (β + β' + β * β') := by
  ext x
  rw [LinearMap.comp_apply, scalingMap_apply h α β, pairing_left h hww hwv,
    pairing_right h hvv hvw, scalingMap_apply, scalingMap_apply]
  module
end GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
