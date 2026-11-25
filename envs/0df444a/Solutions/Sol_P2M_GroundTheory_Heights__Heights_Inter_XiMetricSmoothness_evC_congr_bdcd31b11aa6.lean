-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_evC_congr_bdcd31b11aa6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:24.818477+00:00
-- url     : https://prove2.me/submissions/667edb3e-1921-476a-b5dd-99038a399b40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
theorem _root_.solution {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) {w w' : (Σ k, ι k) → ℂ}
    (h : ∀ p : Σ k, ι k, a p.1 ≠ 0 → w p = w' p) : evC f w = evC f w' := by
  unfold evC
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq']
  refine Finset.sum_congr rfl fun d hd => ?_
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases hp : a p.1 = 0
  · have h0 : d p = 0 := by
      have hs := hf d hd p.1
      rw [hp] at hs
      exact (Finset.sum_eq_zero_iff.1 hs) p.2 (Finset.mem_univ _)
    rw [h0, pow_zero, pow_zero]
  · rw [h p hp]
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
