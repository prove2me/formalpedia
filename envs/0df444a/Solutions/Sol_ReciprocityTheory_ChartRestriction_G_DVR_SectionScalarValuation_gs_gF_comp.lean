-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.gs_gF_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:44.947355+00:00
-- url     : https://prove2.me/submissions/283fa604-d8ea-49e2-8a34-077cbd95f06e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}
namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
theorem _root_.solution {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hf : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    (y : (DegPre.BF D.toPre F).left) (ζ : F) :
    gs h y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ (gF D.toPre F ζ) := by
  calc gs h y ⊤ (gF D.toPre F ζ)
      = gs (h ≫ (fst (TF (R := V) F) D.toPre.P.A).left) y ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) :=
        gs_pull h (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp) _
    _ = gs (𝟙 _ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) y ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by rw [hf, Category.id_comp]
    _ = gs (𝟙 _) y ⊤ (gF D.toPre F ζ) :=
        (gs_pull (𝟙 _) (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp) _).symm
end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
