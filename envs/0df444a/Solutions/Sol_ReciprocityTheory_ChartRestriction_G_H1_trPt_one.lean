-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.trPt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:17.984418+00:00
-- url     : https://prove2.me/submissions/70a82e01-7758-43b7-8d40-29fba3b9dbe3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_FinOrdExists
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution : DegPre.trPt D F 1 = 𝟙 _ := by
  have h1 : fst (TF (R := R) F) D.P.A ≫ (1 : TF (R := R) F ⟶ D.P.A) = 1 := by
    show _ ≫ (toUnit _ ≫ η) = toUnit _ ≫ η
    rw [comp_toUnit_assoc]
  simp only [DegPre.trPt, h1]
  rw [show padd D.P.A (D.prB F) 1 = D.prB F * 1 from rfl, _root_.mul_one]
  first
    | exact lift_fst_snd
    | (simp [DegPre.prB]; done)
    | (unfold DegPre.prB; clear * -; done)
end ReciprocityTheory.ChartRestriction.G.H1
