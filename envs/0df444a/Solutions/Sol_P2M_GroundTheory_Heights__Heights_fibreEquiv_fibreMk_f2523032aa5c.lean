-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fibreEquiv_fibreMk_f2523032aa5c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:48:06.374247+00:00
-- url     : https://prove2.me/submissions/7941f914-3cd3-46c0-a90a-ea6c901a96f7

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FinrankFibreAtOfIsInvertibleSheaf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_stalkEquiv_apply_215b710176b6

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
    (he : IsBasisOn ((preMod X).obj L) U e) (c : Via φ) (r : locRing X p) :
    fibreEquiv φ hp he (fibreMk L φ c (r • germM hp e)) = Via.ofComplex φ (φ r) * c := by
  have : (stalkEquiv hp he).symm (r • germM hp e) = r := by
    rw [LinearEquiv.symm_apply_eq, stalkEquiv_apply]
  change TensorProduct.AlgebraTensorModule.rid (locRing X p) (Via φ) (Via φ) (c ⊗ₜ (stalkEquiv hp he).symm
    (r • germM hp e)) = _
  rw [this, TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
  rfl
end GroundTheory.Heights₂.Heights
