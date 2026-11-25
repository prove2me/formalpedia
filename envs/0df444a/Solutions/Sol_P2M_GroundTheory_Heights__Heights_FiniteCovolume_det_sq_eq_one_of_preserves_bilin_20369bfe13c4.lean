-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_sq_eq_one_of_preserves_bilin_20369bfe13c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:32:37.800497+00:00
-- url     : https://prove2.me/submissions/9c0b92cb-fcfd-4ddf-9279-09ca357d1289

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qm9_det_sq_eq_one_of_preserves_bilin__0c529749593d
import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetSqEqOneOfPreservesBilin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Module
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (f : V →ₗ[ℝ] V) (hf : ∀ x y, B (f x) (f y) = B x y) : LinearMap.det f ^ 2 = 1 :=
  _root_.P2M_UpperTheory_Reformulated_B_Qm9_det_sq_eq_one_of_preserves_bilin__0c529749593d B hB f hf
end GroundTheory.Heights₂.Heights.FiniteCovolume
