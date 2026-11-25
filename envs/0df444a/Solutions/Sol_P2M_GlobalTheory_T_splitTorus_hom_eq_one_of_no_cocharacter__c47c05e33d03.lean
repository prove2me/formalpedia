-- Prove2me | solution 1 for P2M_GlobalTheory_T_splitTorus_hom_eq_one_of_no_cocharacter__c47c05e33d03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:12.966011+00:00
-- url     : https://prove2.me/submissions/6b592d5d-b6b2-49b4-ad59-20441d813099

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusHomEqOneOfNoCocharacter
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusHomEqOneOfNoCocharacterStatement
import Theorems.Thm_GlobalTheory_SS_splitTorus_hom_eq_one_of_no_cocharacter


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
theorem _root_.solution : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], (∀ f : Gm S ⟶ B, IsMonHom f → f = 1) → ∀ u : splitTorus S X ⟶ B, IsMonHom u → u = 1 := by
  first | exact @GlobalTheory.SS.splitTorus_hom_eq_one_of_no_cocharacter | exact GlobalTheory.SS.splitTorus_hom_eq_one_of_no_cocharacter | (intros; apply GlobalTheory.SS.splitTorus_hom_eq_one_of_no_cocharacter <;> assumption)
end _root_.GlobalTheory.T
