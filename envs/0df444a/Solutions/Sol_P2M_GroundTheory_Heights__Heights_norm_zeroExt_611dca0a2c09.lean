-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_norm_zeroExt_611dca0a2c09
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:15.976345+00:00
-- url     : https://prove2.me/submissions/6a0f9886-2b7e-4249-a8d6-38437c325c0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass

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
open MvPolynomial MeasureTheory Module
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (m k : ℕ) (x : EuclideanSpace ℂ (Fin m)) : ‖zeroExt m k x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, zeroExt, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_add]
  simp
end GroundTheory.Heights₂.Heights
