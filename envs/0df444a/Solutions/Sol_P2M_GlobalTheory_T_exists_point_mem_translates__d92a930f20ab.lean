-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_point_mem_translates__d92a930f20ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:40.775346+00:00
-- url     : https://prove2.me/submissions/ac3afe1e-1128-461b-968c-eb000d579a06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPointMemTranslates
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPointMemTranslatesStatement
import Theorems.Thm_GlobalTheory_AlgClosedFibre_exists_point_mem_translates


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S), IrreducibleSpace (Over.mk t ⊗ P.A).left → ∀ (U : (Over.mk t ⊗ P.A).left.Opens), (U : Set (Over.mk t ⊗ P.A).left).Nonempty → ∀ (a c : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)), ∃ u : Over.mk t ⟶ P.A, (lift (𝟙 (Over.mk t)) (c * u * a)).left p ∈ U ∧ (lift (𝟙 (Over.mk t)) (u⁻¹ * a)).left p ∈ U := by
  first | exact @GlobalTheory.AlgClosedFibre.exists_point_mem_translates | exact GlobalTheory.AlgClosedFibre.exists_point_mem_translates | (intros; apply GlobalTheory.AlgClosedFibre.exists_point_mem_translates <;> assumption)
end _root_.GlobalTheory.T
