-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fibreEquiv_value_d97fc2878f25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:09.185386+00:00
-- url     : https://prove2.me/submissions/16a7286f-f4a3-425e-a612-53a6fffda0d4

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FinrankFibreAtOfIsInvertibleSheaf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreEquiv_fibreMk_f2523032aa5c

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
    (he : IsBasisOn ((preMod X).obj L) U e) : fibreEquiv φ hp he (value φ hp e) = 1 := by
  have := fibreEquiv_fibreMk (φ := φ) hp he 1 1
  rw [one_smul, map_one, mul_one] at this
  exact this
end GroundTheory.Heights₂.Heights
