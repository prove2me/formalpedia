-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.smul_int_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:25.957273+00:00
-- url     : https://prove2.me/submissions/6849a588-535f-4e46-ae58-00feaadff12e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
theorem _root_.solution {α : E} (hα : IsIntegral ℤ α) {v : Fin r → E} (hv : v ∈ X.Λ) : α • v ∈ X.Λ := by
  obtain ⟨γ, hγ⟩ : ∃ γ : 𝓞 E, (γ : E) = α := ⟨⟨_, hα⟩, rfl⟩
  have h := X.Λ.smul_mem γ hv
  rw [← algebraMap_smul E γ v] at h
  rw [← hγ]
  exact h
end ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
