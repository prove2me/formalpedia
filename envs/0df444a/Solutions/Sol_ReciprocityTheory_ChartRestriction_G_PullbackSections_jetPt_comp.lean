-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:29:44.657146+00:00
-- url     : https://prove2.me/submissions/c44d4fbb-c499-4046-a002-9ef4e6e9a68c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__comp_88757af08841
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_jet__loc_e980629664a9
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_hom_ext_of_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_appLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_closedPoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_nbhdPt_comp_appLE


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
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {g : ℕ} {Y Y' : Scheme.{0}}
set_option backward.isDefEq.respectTransparency false
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (φ : Y ⟶ Y')
    (e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y')) (hol' : IsHolFam e') (he : ∀ z, e z ≫ φ = e' z) (m : ℕ) :
    jetPt e hol m ≫ φ = jetPt e' hol' m := by
  have hpt : (jetPt e hol m ≫ φ) (IsLocalRing.closedPoint _) = jetPt e' hol' m (IsLocalRing.closedPoint _) := by
    rw [Scheme.Hom.comp_apply, jetPt_closedPoint, jetPt_closedPoint, ← he 0, Scheme.Hom.comp_apply]
  refine hom_ext_of_local hpt fun U h₁ h₂ => ?_
  have hU : e' 0 cpt ∈ U := by
    have : jetPt e' hol' m (IsLocalRing.closedPoint _) ∈ U :=
      h₂ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [jetPt_closedPoint] at this
  have hU' : φ (e 0 cpt) ∈ U := by
    rw [← Scheme.Hom.comp_apply, he 0]; exact hU
  have k := nbhdPt_comp_appLE (y₀ := e 0 cpt) φ (jetψ e hol m) (jetψ_res e hol m) (jetψ_loc e hol m) U hU' h₁
  refine (k : (jetPt e hol m ≫ φ).appLE U ⊤ h₁ = _).trans ?_
  rw [jetPt_appLE e' hol' m U hU h₂, ← Category.assoc]
  congr 1
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  congr 1
  funext z
  rw [valAt'_comp, he z]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
