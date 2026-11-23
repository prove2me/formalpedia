-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TWM.exists_liftO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:40.323782+00:00
-- url     : https://prove2.me/submissions/891cc22a-cf92-4369-bc95-d6cb543e1cdd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LiftOUnique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWM_TF_hom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWO_exists_lift


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
theorem _root_.solution (b : TF (R := V) F ⟶ D.toPre.P.A) : ∃ m : TO hϖ hv ⟶ D.toPre.P.A, ιS hϖ hv ≫ m = b := by
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨x', hx'p, hx'⟩ := TWO.exists_lift v hϖ hv D.toPre.P.A.hom b.left (by rw [Over.w b, TF_hom])
  exact ⟨Over.homMk x' hx'p, Over.OverMorphism.ext hx'⟩
end ReciprocityTheory.ChartRestriction.G.DVR.TWM
