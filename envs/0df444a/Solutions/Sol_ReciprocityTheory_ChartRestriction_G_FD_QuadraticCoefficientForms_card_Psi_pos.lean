-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:26.179752+00:00
-- url     : https://prove2.me/submissions/1b0870d9-3085-4891-9631-389a5371b47e

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
theorem _root_.solution : 0 < Fintype.card X.Ψ := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(Classical.arbitrary (InfinitePlace E)).embedding⟩
  rw [Fintype.card_pos_iff]
  by_cases h : φ ∈ X.Ψ
  · exact ⟨⟨φ, h⟩⟩
  · exact ⟨⟨ComplexEmbedding.conjugate φ, by
      by_contra hc
      exact h ((X.cmType φ).2 hc)⟩⟩
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
