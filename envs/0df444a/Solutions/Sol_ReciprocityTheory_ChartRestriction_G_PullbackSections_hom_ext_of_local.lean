-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:45.291912+00:00
-- url     : https://prove2.me/submissions/100c4129-014e-4a58-a4ec-586ed48eb9c0

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_germ_stalkClosedPointTo_eq

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
variable {Y : Scheme.{0}}
set_option backward.isDefEq.respectTransparency false
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {R : CommRingCat.{0}} [IsLocalRing R] {f₁ f₂ : Spec R ⟶ Y}
    (hpt : f₁ (IsLocalRing.closedPoint R) = f₂ (IsLocalRing.closedPoint R))
    (happ : ∀ (U : Y.Opens) (h₁ : ⊤ ≤ f₁ ⁻¹ᵁ U) (h₂ : ⊤ ≤ f₂ ⁻¹ᵁ U), f₁.appLE U ⊤ h₁ = f₂.appLE U ⊤ h₂) :
    f₁ = f₂ := by
  apply (SpecToEquivOfLocalRing Y R).injective
  refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨hpt, ?_⟩
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  change Y.presheaf.germ U (f₁ (IsLocalRing.closedPoint R)) hU ≫ Scheme.stalkClosedPointTo f₁ =
    Y.presheaf.germ U (f₁ (IsLocalRing.closedPoint R)) hU ≫ (Y.presheaf.stalkCongr _).hom ≫
      Scheme.stalkClosedPointTo f₂
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_assoc, germ_stalkClosedPointTo_eq,
    germ_stalkClosedPointTo_eq, happ]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
