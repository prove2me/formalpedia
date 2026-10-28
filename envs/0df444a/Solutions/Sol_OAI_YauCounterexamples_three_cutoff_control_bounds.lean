-- Prove2me | solution 1 for OAI.YauCounterexamples.three_cutoff_control_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:19:54.37947+00:00
-- url     : https://prove2.me/submissions/3fa63c85-693e-47a2-867b-02781d3b7e6b

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A000
import Definitions.Def_OAIQ070A001
import Definitions.Def_OAIQ070A003
import Definitions.Def_OAIQ070A004

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartGradientProjectionSmooth
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_nonneg (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    0 ≤ coordinateGradientPair g u u x := by
  have hp := (metricCoefficients_posDef g x
    ((chartAt E x).map_source (mem_chart_source E x))).inv.posSemidef.dotProduct_mulVec_nonneg
    (fun i => fderiv ℝ (u ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i))
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at hp
  convert hp using 1; try rfl
  unfold coordinateGradientPair
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeCutoffControlBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

lemma three_cutoff_control_bounds_oai
    (g : SmoothMetric ThreeModel ThreeManifold) (β χ v : ThreeManifold → ℝ)
    (hχrange : ∀ q, χ q ∈ Icc (0:ℝ) 1) {η G Λ : ℝ}
    (hηhalf : η < 1/2) (hvsmall : ∀ q, |v q-1| ≤ η)
    (hGl : G*η < 1/32) (hGgrad : G*η < 1/4096)
    (hΛ : 1 ≤ Λ)
    (hctrl : ∀ q, |weightedLaplacian g β (cutoffFactor χ v) q| ≤ G*η ∧
      Real.sqrt (coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) q) ≤ G*η) :
    (∀ q, 1/2 ≤ cutoffFactor χ v q ∧ cutoffFactor χ v q ≤ 2) ∧
    (∀ q, coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) q ≤ 1/4096) ∧
    (∀ q, |Λ⁻¹*cutoffFactor χ v q*weightedLaplacian g β (cutoffFactor χ v) q| ≤ 1/16) := by
  let w := cutoffFactor χ v
  have hwsmall (q : ThreeManifold) : |w q-1| ≤ 1/2 := by
    change |1+χ q*(v q-1)-1| ≤ _
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg (hχrange q).1]
    exact (mul_le_mul_of_nonneg_right (hχrange q).2 (abs_nonneg _)).trans
      (by simpa using (hvsmall q).trans hηhalf.le)
  have hwl (q : ThreeManifold) : 1/2 ≤ w q := by have := (abs_le.mp (hwsmall q)).1; linarith
  have hwu (q : ThreeManifold) : w q ≤ 2 := by have := (abs_le.mp (hwsmall q)).2; linarith
  have hwp (q : ThreeManifold) : 0 < w q := by linarith [hwl q]
  refine ⟨fun q => ⟨hwl q,hwu q⟩,?_,?_⟩
  · intro q
    have hp0 := coordinateGradientPair_nonneg g w q
    have hs0 := Real.sqrt_nonneg (coordinateGradientPair g w w q)
    have hs2 := Real.sq_sqrt hp0
    have hsle : Real.sqrt (coordinateGradientPair g w w q) ≤ G*η := (hctrl q).2
    have hs1 : Real.sqrt (coordinateGradientPair g w w q) ≤ 1 := by linarith
    nlinarith
  · intro q
    have hΛ0 : 0 ≤ Λ⁻¹ := inv_nonneg.mpr (zero_le_one.trans hΛ)
    have hΛi : Λ⁻¹ ≤ 1 := by
      simpa using (inv_le_inv₀ (zero_lt_one.trans_le hΛ) (show (0:ℝ)<1 by norm_num)).mpr hΛ
    change |Λ⁻¹*w q*weightedLaplacian g β w q| ≤ _
    rw [abs_mul,abs_mul,abs_of_nonneg hΛ0,abs_of_pos (hwp q)]
    calc
      _ ≤ (1*2)*(G*η) := mul_le_mul (mul_le_mul hΛi (hwu q) (hwp q).le (by norm_num))
        (hctrl q).1 (abs_nonneg _) (by norm_num)
      _ ≤ 1/16 := by linarith

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.three_cutoff_control_bounds_oai := @OAI.YauCounterexamples.three_cutoff_control_bounds_oai
