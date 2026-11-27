-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_value_ne_zero_9e9fada13d9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:12:12.540998+00:00
-- url     : https://prove2.me/submissions/7a2f2f1b-6dc7-4d6b-be71-bd70c767aae5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FinrankFibreAtOfIsInvertibleSheaf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreEquiv_value_d97fc2878f25

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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {X : Scheme.{u}} (L : X.Modules)
variable {L}
variable {p : X} {φ : locRing X p →+* ℂ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : value φ hp e ≠ 0 := by
  intro h
  have := fibreEquiv_value (φ := φ) hp he
  rw [h, map_zero] at this
  exact zero_ne_one this
end GroundTheory.Heights₂.Heights
