-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermitianForm_eq_zero_of_toSesq_eq_zero_63137fd96ad2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:51.013203+00:00
-- url     : https://prove2.me/submissions/9ed63def-f67c-4a7c-82b2-11297fcef8e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StTraceHermNondegenerate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTraceHermNondegenerate

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
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace HermitianForm
theorem _root_.solution (h : HermitianForm F E W) {x : W}
    (hx : ∀ w, h.toSesq x w = 0) : x = 0 := by
  apply h.nonsingular.1
  rw [map_zero]
  exact LinearMap.ext hx
end HermitianForm
end GroundTheory.Heights₂.Heights.FiniteCovolume
