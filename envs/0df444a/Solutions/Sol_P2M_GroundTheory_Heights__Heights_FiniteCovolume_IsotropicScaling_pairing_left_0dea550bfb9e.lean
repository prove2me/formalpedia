-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_pairing_left_0dea550bfb9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:10.807118+00:00
-- url     : https://prove2.me/submissions/4b0b601e-3424-4a74-8137-771281259eb8

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
theorem _root_.solution (hww : h.toSesq w w = 0) (hwv : h.toSesq w v = 1) (α β : E) (x : W) :
    h.toSesq w (scalingMap h v w α β x) = (1 + α) * h.toSesq w x := by
  rw [scalingMap_apply, map_add, map_add, map_smul, map_smul, hwv, hww, smul_eq_mul, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
