-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.integrable_normSq_combination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:01:19.397603+00:00
-- url     : https://prove2.me/submissions/7aa1bb60-3d08-4bc6-ba31-3972af77ee6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {X : Type*} [MeasurableSpace X] {μ : Measure X} {r : ℕ}
    (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (c : Fin r → ℂ) : Integrable (fun x => ‖∑ i, c i * s i x‖ ^ 2 * w x) μ := by
  have hg : Integrable (fun x => ∑ i, ∑ j, (starRingEnd ℂ (c i) * c j) *
      (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _
  refine hg.re.congr (ae_of_all _ fun x => ?_)
  have h : ((‖∑ i, c i * s i x‖ ^ 2 * w x : ℝ) : ℂ) = ∑ i, ∑ j, (starRingEnd ℂ (c i) * c j) *
      (starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) := by
    rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, map_sum,
      Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul]
    ring
  dsimp only
  rw [← h]
  rfl
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
