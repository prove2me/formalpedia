-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds.abs_norm_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:00.708799+00:00
-- url     : https://prove2.me/submissions/d39f4615-9d3f-4510-9407-0547b9c40e4a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
open NumberField Complex Module Matrix
open scoped ComplexConjugate nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
theorem _root_.solution {x : E} {a : ℝ} (h : ∀ σ : E →+* ℂ, ‖σ x‖ = a) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = a ^ finrank ℚ E := by
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ = a ^ finrank ℚ E := by
    rw [h1, norm_prod, Finset.prod_congr rfl (fun σ _ => h σ.toRingHom), Finset.prod_const,
      Finset.card_univ, AlgHom.card]
  rw [← h2, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
end ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
