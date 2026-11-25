-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.comb_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:46:42.048435+00:00
-- url     : https://prove2.me/submissions/22a95a2b-bc83-4e1e-aea5-ae2adc2c3908

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_comp_le_Qy

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
theorem _root_.solution (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ) {ι : Type} [Fintype ι]
    (q : ι → ℚ) (f : ι → Fin r → E) (b : Fin r) :
    ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (∑ i, q i • f i)) b‖ ≤
      ∑ i, ‖(q i : ℂ)‖ * (1 + QuadraticLatticeForms.Qy X y (f i) / X.c τ) := by
  have hcpos : 0 < X.c τ := by
    unfold Data.c
    have := (map_ne_zero τ.1).2 X.ξ0_ne
    positivity
  have hemb : Data.emb τ.1 (∑ i, q i • f i) = ∑ i, (q i : ℂ) • Data.emb τ.1 (f i) := by
    funext a
    simp [Data.emb, map_sum, Finset.sum_apply, Rat.smul_def, map_mul, map_ratCast]
  have hlin : ((y τ)⁻¹ *ᵥ Data.emb τ.1 (∑ i, q i • f i)) b =
      ∑ i, (q i : ℂ) * ((y τ)⁻¹ *ᵥ Data.emb τ.1 (f i)) b := by
    rw [hemb, Matrix.mulVec_sum, Finset.sum_apply]
    simp [Matrix.mulVec_smul]
  rw [hlin]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 := comp_le_Qy X y τ (f i) b
  have h2 : ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (f i)) b‖ ^ 2 ≤ QuadraticLatticeForms.Qy X y (f i) / X.c τ := by
    rw [le_div_iff₀ hcpos]
    linarith
  nlinarith [sq_nonneg (‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (f i)) b‖ - 1)]
end ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
