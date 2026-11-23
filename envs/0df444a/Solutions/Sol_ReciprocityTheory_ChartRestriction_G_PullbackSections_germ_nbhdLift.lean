-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.germ_nbhdLift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:45.656154+00:00
-- url     : https://prove2.me/submissions/26f5e1fd-503a-4132-ac1c-ea47a863ace4

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
theorem _root_.solution (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU) (U : Y.Opens) (hU : y₀ ∈ U) :
    Y.presheaf.germ U y₀ hU ≫ nbhdLift y₀ A ψ hψ = ψ U hU := by
  exact Limits.colimit.ι_desc _ _
end ReciprocityTheory.ChartRestriction.G.PullbackSections
