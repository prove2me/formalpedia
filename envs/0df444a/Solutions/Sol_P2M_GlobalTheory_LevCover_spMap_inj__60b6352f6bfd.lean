-- Prove2me | solution 1 for P2M_GlobalTheory_LevCover_spMap_inj__60b6352f6bfd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:47:21.676904+00:00
-- url     : https://prove2.me/submissions/0cbc8dac-46dd-4351-871d-634cbd8bc4c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCoprimeZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}
namespace GlobalTheory.LevCover
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)
end GlobalTheory.LevCover
