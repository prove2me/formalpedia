-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TangentJacComp_adjoint_restrictScalars_6c2dd86bcf0a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:51.9518+00:00
-- url     : https://prove2.me/submissions/cd5e8cf1-b2f6-4840-b7d2-dbc26001f358

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacComp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentJacComp
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentJacComp_real_inner_eq_re_595de423dd88

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
namespace GroundTheory.Heights₂.Heights
namespace TangentJacComp
theorem _root_.solution {d n : ℕ}
    (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    LinearMap.adjoint (L.restrictScalars ℝ) = (LinearMap.adjoint L).restrictScalars ℝ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [TangentJacComp.real_inner_eq_re, TangentJacComp.real_inner_eq_re]
  simp [LinearMap.adjoint_inner_left]
end TangentJacComp
end GroundTheory.Heights₂.Heights
