-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.toCP_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:50.421739+00:00
-- url     : https://prove2.me/submissions/a167eebb-f3f0-4c06-b914-1a1bf0a1931e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Classical
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
theorem _root_.solution : Function.Bijective (toCP X) := by
  constructor
  · rintro ⟨τ, hτ⟩ ⟨τ', hτ'⟩ h
    have h' : InfinitePlace.mk τ = InfinitePlace.mk τ' := congrArg Subtype.val h
    rcases InfinitePlace.mk_eq_iff.1 h' with e | e
    · exact Subtype.ext e
    · exfalso
      rw [← e] at hτ'
      exact (X.cmType τ).1 hτ hτ'
  · rintro ⟨w, hw⟩
    by_cases hφ : w.embedding ∈ X.Ψ
    · exact ⟨⟨_, hφ⟩, Subtype.ext (InfinitePlace.mk_embedding w)⟩
    · have hc : ComplexEmbedding.conjugate w.embedding ∈ X.Ψ := by
        by_contra hc
        exact hφ ((X.cmType _).2 hc)
      exact ⟨⟨_, hc⟩, Subtype.ext ((InfinitePlace.mk_conjugate_eq _).trans (InfinitePlace.mk_embedding w))⟩
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
