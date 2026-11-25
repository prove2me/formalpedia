-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_pairing_right_8c8b388a4a3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:00.390089+00:00
-- url     : https://prove2.me/submissions/188b1e43-4af5-4198-8942-33083ee76adf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIsotropicScaling
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_apply_eff752ab2046

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
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
theorem _root_.solution (hvv : h.toSesq v v = 0) (hvw : h.toSesq v w = 1) (α β : E) (x : W) :
    h.toSesq v (scalingMap h v w α β x) = (1 + β) * h.toSesq v x := by
  rw [scalingMap_apply, map_add, map_add, map_smul, map_smul, hvv, hvw, smul_eq_mul, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
