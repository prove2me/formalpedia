-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.finrank_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:00:19.065958+00:00
-- url     : https://prove2.me/submissions/84e85e80-2cd8-4b9b-992c-d1afb1e703d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_two_card_Psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
open NumberField Module Submodule
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
theorem _root_.solution : finrank ℝ (X.Ψ → ℂ) = finrank ℚ E := by
  rw [Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← two_card_Psi X]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
