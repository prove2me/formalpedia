-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.emb_dual_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:36:27.330085+00:00
-- url     : https://prove2.me/submissions/a4b2b471-2839-4312-9968-72e80cb07147

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pN_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_emb_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (x ξ : Vsp dim) (y : E)
    (hy : ∀ β : 𝓞 E, ((Algebra.trace ℚ E ((β : E) * y) : ℚ) : ℝ) = (Hf x (act β ξ)).im) (σ : E →+* ℂ)
    (hn : nS ξ σ = 0) : σ y = 0 := by
  have h1 : pN ξ σ = 0 := by
    have := pN_nonneg ξ σ; have := pN_nonneg ξ (ComplexEmbedding.conjugate σ); rw [nS] at hn; linarith
  have h2 : pN ξ (ComplexEmbedding.conjugate σ) = 0 := by
    have := pN_nonneg ξ σ; have := pN_nonneg ξ (ComplexEmbedding.conjugate σ); rw [nS] at hn; linarith
  have hz : ∀ τ, pN ξ τ = 0 → hA x ξ τ = 0 := by
    intro τ hτ
    have : ∀ a, ξ ⟨τ, a⟩ = 0 := by
      intro a
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).1 hτ a (Finset.mem_univ a)
      simpa using h
    simp [hA, this]
  rw [emb_dual x ξ y hy σ, hz _ h2, hz _ h1]
  simp
end ReciprocityTheory.ChartRestriction.G.I2
