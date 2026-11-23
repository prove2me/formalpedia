-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.nbhdPt_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:17.138679+00:00
-- url     : https://prove2.me/submissions/1bc7add0-0dc5-492c-b813-8df3d601df1d

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_germ_stalkClosedPointTo_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_germ_nbhdLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isLocalHom_nbhdLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_nbhdPt_closedPoint

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
theorem _root_.solution [IsLocalRing A] (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hloc : ∀ (U : Y.Opens) (hU : y₀ ∈ U) (f : Γ(Y, U)), IsUnit (ψ U hU f) → y₀ ∈ Y.basicOpen f)
    (U : Y.Opens) (hU : y₀ ∈ U) (h : ⊤ ≤ nbhdPt ψ hψ ⁻¹ᵁ U) :
    (nbhdPt ψ hψ).appLE U ⊤ h = ψ U hU ≫ (Scheme.ΓSpecIso A).inv := by
  have := isLocalHom_nbhdLift ψ hψ hloc
  have hpt := nbhdPt_closedPoint ψ hψ hloc
  have hU' : nbhdPt ψ hψ (IsLocalRing.closedPoint A) ∈ U := by rw [hpt]; exact hU
  have k := germ_stalkClosedPointTo_eq (nbhdPt ψ hψ) U hU'
  have k2 := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (nbhdLift y₀ A ψ hψ) U hU'
  rw [germ_nbhdLift] at k2
  have k3 : (nbhdPt ψ hψ).appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem _ hU').ge ≫
      (Scheme.ΓSpecIso A).hom = ψ U hU := k.symm.trans k2
  rw [← k3]
  simp
end ReciprocityTheory.ChartRestriction.G.PullbackSections
