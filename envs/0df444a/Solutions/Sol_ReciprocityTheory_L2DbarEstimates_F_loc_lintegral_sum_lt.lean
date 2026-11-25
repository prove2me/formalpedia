-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.loc_lintegral_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:20:59.160097+00:00
-- url     : https://prove2.me/submissions/cb6a13e6-4ad4-4426-90ed-7fb4bda97466

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [MeasurableSpace M] (μ : Measure M) {N : ℕ}
    (F : M → ℝ≥0∞) (f : Fin N → M → ℝ≥0∞) (hf : ∀ i, AEMeasurable (f i) μ)
    (hle : ∀ x, F x ≤ N * ∑ i, f i x) (δ' δ : ℝ≥0∞) (hi : ∀ i, ∫⁻ x, f i x ∂μ < δ')
    (hδ : δ' * (N * N) < δ) : ∫⁻ x, F x ∂μ < δ := by
  calc ∫⁻ x, F x ∂μ ≤ ∫⁻ x, N * ∑ i, f i x ∂μ := lintegral_mono hle
    _ = N * ∑ i, ∫⁻ x, f i x ∂μ := by
      rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N), lintegral_finset_sum' _ (fun i _ => hf i)]
    _ ≤ N * ∑ _i : Fin N, δ' := by
      gcongr with i
      exact (hi i).le
    _ = δ' * (N * N) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ < δ := hδ
end ReciprocityTheory.L2DbarEstimates.F
