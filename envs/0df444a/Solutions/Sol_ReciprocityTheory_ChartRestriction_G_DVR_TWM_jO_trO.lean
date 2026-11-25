-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TWM.jO_trO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:35.259366+00:00
-- url     : https://prove2.me/submissions/61861d1f-6eb1-4a67-82db-193f80052727

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LiftOUnique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWM_trO_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWM_trO_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_fst


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
theorem _root_.solution (b : TF (R := V) F ⟶ D.toPre.P.A) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = b) :
    jO hϖ hv (D := D) ≫ trO hϖ hv m = DegPre.trPt D.toPre F b ≫ jO hϖ hv := by
  have h1 : jO hϖ hv (D := D) ≫ trO hϖ hv m ≫ snd (TO hϖ hv) D.toPre.P.A =
      snd (TF (R := V) F) D.toPre.P.A * (fst (TF (R := V) F) D.toPre.P.A ≫ b) := by
    rw [trO_snd, MonObj.comp_mul, whiskerRight_snd, ← Category.assoc, whiskerRight_fst, Category.assoc, hm]
  have h2 : DegPre.trPt D.toPre F b ≫ jO hϖ hv (D := D) ≫ snd (TO hϖ hv) D.toPre.P.A =
      snd (TF (R := V) F) D.toPre.P.A * (fst (TF (R := V) F) D.toPre.P.A ≫ b) := by
    rw [whiskerRight_snd]
    unfold DegPre.trPt
    rw [lift_snd]
    rfl
  have h3 : jO hϖ hv (D := D) ≫ trO hϖ hv m ≫ fst (TO hϖ hv) D.toPre.P.A =
      fst (TF (R := V) F) D.toPre.P.A ≫ ιS hϖ hv := by
    rw [trO_fst, whiskerRight_fst]
  have h4 : DegPre.trPt D.toPre F b ≫ jO hϖ hv (D := D) ≫ fst (TO hϖ hv) D.toPre.P.A =
      fst (TF (R := V) F) D.toPre.P.A ≫ ιS hϖ hv := by
    rw [whiskerRight_fst, ← Category.assoc, tr_fst]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc]
    rw [h3, h4]
  · simp only [Category.assoc]
    rw [h1, h2]
end ReciprocityTheory.ChartRestriction.G.DVR.TWM
