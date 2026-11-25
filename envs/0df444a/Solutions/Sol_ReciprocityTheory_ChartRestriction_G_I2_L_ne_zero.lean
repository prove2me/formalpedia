-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.L_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:55:28.567077+00:00
-- url     : https://prove2.me/submissions/2c4ef4b1-a347-4dc0-ac10-878b690a6dde

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsMaximal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (X : PT E) (hr : 1 ≤ X.r) (τ : E →+* ℂ) : ∃ x ∈ X.L, x ≠ 0 := by
  have hpos : 0 < Fintype.card (Idx X.dim) := by
    have h := X.dim_conj τ
    rw [Fintype.card_pos_iff]
    by_cases h0 : 0 < X.dim τ
    · exact ⟨⟨τ, ⟨0, h0⟩⟩⟩
    · exact ⟨⟨NumberField.ComplexEmbedding.conjugate τ, ⟨0, by omega⟩⟩⟩
  exact ⟨X.b ⟨0, by omega⟩, Submodule.subset_span (Set.mem_range_self _), X.b.ne_zero _⟩
end ReciprocityTheory.ChartRestriction.G.I2
