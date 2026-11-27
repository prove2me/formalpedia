-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.gs_gF_zF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:30:21.278348+00:00
-- url     : https://prove2.me/submissions/21d7455d-c45b-482e-bcb0-ce486eb696d0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsValGenHasVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GsScalJFK

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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}
namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
theorem _root_.solution (y : (TF (R := V) F).left) (ζ : F) :
    gs (DegPre.zF D.toPre F).left y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by
  have h := gs_pull (DegPre.zF D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp)
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ)
  have e : (DegPre.zF D.toPre F).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left]
    simp [DegPre.zF]
  rw [e] at h
  rw [← h]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
