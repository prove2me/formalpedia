-- Prove2me | solution 1 for P2M_GlobalTheory_AbLaw_PowVanish_pre_inf__f58b070a9db0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:50:31.210851+00:00
-- url     : https://prove2.me/submissions/29eb5e8c-8dd8-40c9-ab4b-5911dfd353c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.PowVanish
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLaw.PowVanish
theorem _root_.solution (h : Y ⟶ X) (U U' : X.Opens) : h ⁻¹ᵁ (U ⊓ U') ≤ h ⁻¹ᵁ U ⊓ h ⁻¹ᵁ U' := fun _ hy => hy
end GlobalTheory.AbLaw.PowVanish
