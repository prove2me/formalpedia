-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.spec_comp_nbhdPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:32:50.702277+00:00
-- url     : https://prove2.me/submissions/bd6d323e-9930-4f48-b29e-7cf421a5bc47

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_nbhdLift_comp

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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {B : CommRingCat.{0}} (χ : A ⟶ B) (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU) :
    Spec.map χ ≫ nbhdPt ψ hψ =
      nbhdPt (fun U hU => ψ U hU ≫ χ) (fun U V hU hV h => by rw [← Category.assoc, hψ]) := by
  simp only [nbhdPt]
  rw [nbhdLift_comp, Spec.map_comp, Category.assoc]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
