-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TWM.liftO_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:28.205537+00:00
-- url     : https://prove2.me/submissions/02d24007-6bb2-4cdb-9b6c-260cf1112a8b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LiftOUnique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWO_lift_unique


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWM
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM
theorem _root_.solution (m₁ m₂ : TO hϖ hv ⟶ D.toPre.P.A) (h : ιS hϖ hv ≫ m₁ = ιS hϖ hv ≫ m₂) : m₁ = m₂ := by
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  apply Over.OverMorphism.ext
  exact TWO.lift_unique v hϖ hv D.toPre.P.A.hom m₁.left m₂.left (Over.w m₁) (Over.w m₂)
    (congrArg (fun g => g.left) h)
end ReciprocityTheory.ChartRestriction.G.DVR.TWM
