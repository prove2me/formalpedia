-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.hermC_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:46:26.85888+00:00
-- url     : https://prove2.me/submissions/cedd85d1-4477-41b3-8c30-1ad3c2a4b1ef

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_hermC_expand

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
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X.Gm u w := by
  rw [hermC_expand X τ γ u w]
  have h1 := hermC_expand X τ 1 u w
  rw [Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.one_mulVec, Matrix.one_mulVec] at h1
  rw [h1]
  simp only [hγ, Matrix.one_mulVec]
end ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
