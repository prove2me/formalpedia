-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.gram_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:04:43.001482+00:00
-- url     : https://prove2.me/submissions/22d40915-51a3-4c85-8841-49922022f4a0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_hermC_stab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
open Matrix NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
theorem _root_.solution {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) : gram τ X.Gm (γ.map τ * Y) = gram τ X.Gm Y := by
  have hc : ∀ a, col (γ.map τ * Y) a = (γ.map τ) *ᵥ col Y a := fun a => by
    funext k
    simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  ext a b
  simp only [gram, Matrix.of_apply, hc, hermC_stab X hγ τ]
end ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
