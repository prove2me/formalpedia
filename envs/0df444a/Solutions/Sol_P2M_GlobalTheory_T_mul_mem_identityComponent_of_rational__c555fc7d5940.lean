-- Prove2me | solution 1 for P2M_GlobalTheory_T_mul_mem_identityComponent_of_rational__c555fc7d5940
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:21.317391+00:00
-- url     : https://prove2.me/submissions/d3942ffb-bcbd-4c4c-b22e-169ae339e3d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulMemIdentityComponentOfRational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulMemIdentityComponentOfRationalStatement
import Theorems.Thm_GlobalTheory_mul_mem_identityComponent_of_rational


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), x.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → (x * y).left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) := by
  first | exact @GlobalTheory.mul_mem_identityComponent_of_rational | exact GlobalTheory.mul_mem_identityComponent_of_rational | (intros; apply GlobalTheory.mul_mem_identityComponent_of_rational <;> assumption)
end _root_.GlobalTheory.T
