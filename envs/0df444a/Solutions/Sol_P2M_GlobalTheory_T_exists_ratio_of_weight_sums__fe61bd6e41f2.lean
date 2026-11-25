-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_ratio_of_weight_sums__fe61bd6e41f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:46:37.41293+00:00
-- url     : https://prove2.me/submissions/0a814bff-ea9e-4512-87eb-272233d4b5a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSums
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSumsStatement
import Theorems.Thm_GlobalTheory_SS_WtRat_exists_ratio_of_weight_sums


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → ∀ (U : G.left.Opens) (f : Γ(G.left, U)), (U : Set G.left).Nonempty → ∃ (U' : G.left.Opens) (h : U' ≤ U) (n : ℕ) (a b : Fin n → Γ(G.left, U')) (χ : Fin n → X), (U' : Set G.left).Nonempty ∧ (∀ j, Wt i U' (a j) (χ j) ∧ Wt i U' (b j) (χ j) ∧ (a j = 0 ∨ IsUnit (a j)) ∧ (b j = 0 ∨ IsUnit (b j))) ∧ IsUnit (∑ j, b j) ∧ (G.left.presheaf.map (homOfLE h).op).hom f * ∑ j, b j = ∑ j, a j := by
  first | exact @GlobalTheory.SS.WtRat.exists_ratio_of_weight_sums | exact GlobalTheory.SS.WtRat.exists_ratio_of_weight_sums | (intros; apply GlobalTheory.SS.WtRat.exists_ratio_of_weight_sums <;> assumption)
end _root_.GlobalTheory.T
