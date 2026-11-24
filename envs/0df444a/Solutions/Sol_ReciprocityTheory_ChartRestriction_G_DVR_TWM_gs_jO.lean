-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TWM.gs_jO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:34.26295+00:00
-- url     : https://prove2.me/submissions/6e4a83c1-cf0f-4b69-97a8-e21c77446525

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWM_appTop_specMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWM_jO_fst

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
theorem _root_.solution {Z : Scheme.{0}} (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (r : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) :
    gs (ρ ≫ (jO hϖ hv (D := D)).left) z ⊤ ((fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom r) =
      gs ρ z ⊤ (gF D.toPre F (ιr (v := v) r)) := by
  have e1 : gs (ρ ≫ (jO hϖ hv (D := D)).left) z ⊤ ((fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom r) =
      gs ((ρ ≫ (jO hϖ hv (D := D)).left) ≫ (fst (TO hϖ hv) D.toPre.P.A).left) z ⊤ r := gs_pull _ _ z ⊤ trivial r
  rw [e1, Category.assoc, jO_fst, ← Category.assoc]
  have e2 : gs ((ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) ≫ (ιS hϖ hv).left) z ⊤ r =
      gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤ ((ιS hϖ hv).left.appTop.hom r) := (gs_pull _ _ z ⊤ trivial r).symm
  have e3 : gs ρ z ⊤ (gF D.toPre F (ιr (v := v) r)) = gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (ιr (v := v) r)) := gs_pull _ _ z ⊤ trivial _
  rw [e2, e3, show (ιS hϖ hv).left = Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) from rfl, appTop_specMap]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR.TWM
