-- Prove2me | solution 1 for P2M_MainStatements_Hodge_Pf_AXO_isPullO_id__c9a67d2b14ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:18.610326+00:00
-- url     : https://prove2.me/submissions/9e617dc2-a75c-448b-b6f8-d6d5545a706a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_eq_of_natTrans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.AXO
variable {R : Type} [CommRing R]
namespace MainStatements.Hodge.Pf.AXO
theorem _root_.solution {X : Scheme.{0}} (s : X ⟶ Sp R) (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R))
    (c : HO1 s) : IsPullO h c c :=
  CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X) (fun _ _ ↦ rfl) c
end MainStatements.Hodge.Pf.AXO
