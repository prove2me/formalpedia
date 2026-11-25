-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.isLocalHom_jetMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:42.698496+00:00
-- url     : https://prove2.me/submissions/d13017f9-0bae-43c7-874d-053590b52bd4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isUnit_of_jetAug
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetAug_jetMap

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
variable {K : Type} [Field K] {ι : Type} {m : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {ι' : Type} (φ : ι → MvPolynomial ι' K) (hφ : ∀ i, φ i ∈ orig K ι') :
    IsLocalHom ((jetMap (m := m) φ hφ : Jet K ι m →ₐ[K] Jet K ι' m) : Jet K ι m →+* Jet K ι' m) := by
  refine ⟨fun a ha => isUnit_of_jetAug a ?_⟩
  rw [← jetAug_jetMap φ hφ a]
  exact (ha.map (jetAug : Jet K ι' m →ₐ[K] K)).ne_zero
end ReciprocityTheory.ChartRestriction.G.PullbackSections
