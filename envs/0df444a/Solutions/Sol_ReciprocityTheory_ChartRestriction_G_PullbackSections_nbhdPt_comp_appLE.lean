-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.nbhdPt_comp_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:27:48.085476+00:00
-- url     : https://prove2.me/submissions/adae7da7-8873-47a5-af51-b4e384028817

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_nbhdPt_appLE

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
variable (y₀ : Y) (A : CommRingCat.{0})
variable {y₀ A}
set_option backward.isDefEq.respectTransparency false
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution [IsLocalRing A] {Y' : Scheme.{0}} (φ : Y ⟶ Y')
    (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hloc : ∀ (U : Y.Opens) (hU : y₀ ∈ U) (f : Γ(Y, U)), IsUnit (ψ U hU f) → y₀ ∈ Y.basicOpen f)
    (U' : Y'.Opens) (hU' : φ y₀ ∈ U') (h : ⊤ ≤ (nbhdPt ψ hψ ≫ φ) ⁻¹ᵁ U') :
    (nbhdPt ψ hψ ≫ φ).appLE U' ⊤ h = φ.app U' ≫ ψ (φ ⁻¹ᵁ U') hU' ≫ (Scheme.ΓSpecIso A).inv := by
  rw [Scheme.Hom.comp_appLE]
  first
  | rw [nbhdPt_appLE ψ hψ hloc (φ ⁻¹ᵁ U') hU']
  | erw [nbhdPt_appLE ψ hψ hloc (φ ⁻¹ᵁ U') hU']
end ReciprocityTheory.ChartRestriction.G.PullbackSections
