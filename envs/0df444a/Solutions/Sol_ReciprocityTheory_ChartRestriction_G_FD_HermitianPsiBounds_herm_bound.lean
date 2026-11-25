-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds.herm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:18:29.368148+00:00
-- url     : https://prove2.me/submissions/5f8c594e-18b5-47dc-b23f-d14fd39e61ce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPsiBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPsiBounds_herm_bound_psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
open Matrix NumberField Complex QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
theorem _root_.solution {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IntegralBasisReduction.IsNormal X y) (σ : E →+* ℂ)
    (p q : Fin r → E) : ‖σ (herm X.Gm p q)‖ ≤ (Qy X y p + Qy X y q) * Cinv X := by
  by_cases hσ : σ ∈ X.Ψ
  · exact herm_bound_psi X hy ⟨σ, hσ⟩ p q
  · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
      rw [X.cmType]
      first
      | (rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ from star_star σ]
         exact hσ)
      | simpa using hσ
    have h := herm_bound_psi X hy ⟨_, hc⟩ p q
    first
    | simpa [ComplexEmbedding.conjugate_coe_eq] using h
    | (simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h; exact h)
end ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
