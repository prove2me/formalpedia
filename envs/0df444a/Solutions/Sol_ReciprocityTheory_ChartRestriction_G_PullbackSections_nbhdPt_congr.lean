-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.nbhdPt_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:27:55.038247+00:00
-- url     : https://prove2.me/submissions/6a610b25-3b9c-4831-b74c-8ef2bbfc0b13

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA

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
theorem _root_.solution {ψ ψ' : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A)}
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hψ' : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ' V hV = ψ' U hU)
    (e : ∀ U hU, ψ U hU = ψ' U hU) : nbhdPt ψ hψ = nbhdPt ψ' hψ' := by
  obtain rfl : ψ = ψ' := funext fun U => funext fun hU => e U hU
  rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections
