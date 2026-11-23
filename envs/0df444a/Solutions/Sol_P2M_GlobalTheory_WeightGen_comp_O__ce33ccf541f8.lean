-- Prove2me | solution 1 for P2M_GlobalTheory_WeightGen_comp_O__ce33ccf541f8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:02.877834+00:00
-- url     : https://prove2.me/submissions/b0b8dc8d-8501-4924-b901-fc3df9dcfede

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeightGen
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.WeightGen
theorem _root_.solution {T T' : Over (Spec (CommRingCat.of R))} (h : T' ⟶ T) (p : T ⟶ D.P.A) (χ : D.X)
    (k : Fin 4) : h.left ≫ D.Oφ p χ k = D.Oφ (h ≫ p) χ k := by
  have e0 : h ≫ padd D.P.A p (toUnit T ≫ D.c χ) = padd D.P.A (h ≫ p) (toUnit T' ≫ D.c χ) := by
    simp only [padd]; rw [← Category.assoc, comp_lift, comp_toUnit_assoc]
  have e1 : h ≫ toUnit T ≫ D.c χ = toUnit T' ≫ D.c χ := by simp
  have e3 : h ≫ toUnit T ≫ η[D.P.A] = toUnit T' ≫ η[D.P.A] := by simp
  fin_cases k
  · exact congrArg (fun g => g.left) e0
  · exact congrArg (fun g => g.left) e1
  · rfl
  · exact congrArg (fun g => g.left) e3
end GlobalTheory.WeightGen
