-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.nbhdLift_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:27:41.981979+00:00
-- url     : https://prove2.me/submissions/da08558a-0211-4089-88a6-a15fbfa7d2a2

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_germ_nbhdLift

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
    nbhdLift y₀ B (fun U hU => ψ U hU ≫ χ) (fun U V hU hV h => by rw [← Category.assoc, hψ]) =
      nbhdLift y₀ A ψ hψ ≫ χ := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  rw [germ_nbhdLift, ← Category.assoc, germ_nbhdLift]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
