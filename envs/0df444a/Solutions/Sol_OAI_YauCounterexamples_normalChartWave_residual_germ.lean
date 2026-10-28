-- Prove2me | solution 1 for OAI.YauCounterexamples.normalChartWave_residual_germ
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:37:56.580904+00:00
-- url     : https://prove2.me/submissions/eab39a4c-1eda-4c17-94aa-cc57b4aa158a

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007
import Theorems.Thm_OAI_YauCounterexamples_normalChartWave_laplacian

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_WaveDeriv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

section WaveDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem contDiff_waveDeriv (v : E) (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (waveDeriv v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

end WaveDifferentiation


end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_WaveDerivCompLinear
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma waveDeriv_comp_linear (A : E →L[ℝ] F) {f : F → ℂ}
    (hf : Differentiable ℝ f) (v x : E) :
    waveDeriv v (f ∘ A) x = waveDeriv (A v) f (A x) := by
  simp only [waveDeriv, fderiv_comp x (hf _) A.differentiableAt,
    ContinuousLinearMap.comp_apply, A.fderiv]

lemma waveCoordinateOperator_comp_linear (A : E →L[ℝ] F)
    (e : Fin 3 → E) (g : Fin 3 → Fin 3 → F → ℂ) (b : Fin 3 → F → ℂ)
    {f : F → ℂ} (hf : ContDiff ℝ ∞ f) (x : E) :
    waveCoordinateOperator e (fun i j => g i j ∘ A) (fun i => b i ∘ A) (f ∘ A) x =
      waveCoordinateOperator (fun i => A (e i)) g b f (A x) := by
  have hD (i : Fin 3) : waveDeriv (e i) (f ∘ A) = waveDeriv (A (e i)) f ∘ A := by
    funext y
    exact waveDeriv_comp_linear A (hf.differentiable (by simp)) (e i) y
  simp only [waveCoordinateOperator, hD, Function.comp_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [waveDeriv_comp_linear A ((contDiff_waveDeriv _ _ hf).differentiable (by simp))]
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffSmoothFiniteWave
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma normalWaveEquiv_single (i : Fin 3) :
    normalWaveEquiv (Pi.single i 1) = EuclideanSpace.basisFun (Fin 3) ℝ i := by
  rw [EuclideanSpace.basisFun_apply]
  rfl


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

lemma normalWavePiOperator_eq (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Fin 3 → ℝ) :
    normalWavePiOperator g q f x =
      waveCoordinateOperator (fun i => Pi.single i 1)
        (fun i j y => ((normalWaveMetric g q (normalWaveEquiv y))⁻¹ i j : ℂ))
        (fun j y => (normalWaveFirstCoefficient g q (normalWaveEquiv y) j : ℂ)) f x := by
  have h := waveCoordinateOperator_comp_linear normalWaveEquiv.toContinuousLinearMap
    (fun i => Pi.single i 1)
    (fun i j y => ((normalWaveMetric g q y)⁻¹ i j : ℂ))
    (fun j y => (normalWaveFirstCoefficient g q y j : ℂ))
    (hf.comp normalWaveEquiv.symm.contDiff) x
  simpa only [normalWavePiOperator,Function.comp_def,ContinuousLinearEquiv.coe_coe,
    normalWaveEquiv_single,ContinuousLinearEquiv.symm_apply_apply] using h.symm

lemma normalWavePiOperator_eq_extension (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (A : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (x : Fin 3 → ℝ)
    (hA : ∀ i j, A i j x = ((normalWaveMetric g q (normalWaveEquiv x))⁻¹ i j : ℂ))
    (hb : ∀ j, b j x = (normalWaveFirstCoefficient g q (normalWaveEquiv x) j : ℂ)) :
    normalWavePiOperator g q f x = waveCoordinateOperator (fun i => Pi.single i 1) A b f x := by
  rw [normalWavePiOperator_eq g q hf]
  simp only [waveCoordinateOperator,hA,hb]



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalChartWave
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] in
lemma smoothChartPush_apply (e : OpenPartialHomeomorph E F) (f : E → V)
    {x : E} (hx : x ∈ e.source) : smoothChartPush e f (e x) = f x := by
  simp only [smoothChartPush,Set.indicator_of_mem (e.map_source hx),Function.comp_apply,
    e.left_inv hx]

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

lemma normalChartWave_apply (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (f : (Fin 3 → ℝ) → ℂ) {x : Fin 3 → ℝ} (hx : normalWaveEquiv x ∈ e.source) :
    normalChartWave e f (e (normalWaveEquiv x)) = f x := by
  simpa only [normalChartWave,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using
    smoothChartPush_apply e (f ∘ normalWaveEquiv.symm) hx



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_NormalWaveMetricCommonPositive
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples

theorem normalChartWave_residual_germ_oai (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (he : (e : NormalWaveSpace → NormalWaveSpace) =
      normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2))
    {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (A : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (lam : ℂ) {R : ℝ}
    (hp : ∀ v : NormalWaveSpace, ‖v‖ < R → 0 < (normalWaveMetric g q v).det)
    (hA : ∀ x, ‖normalWaveEquiv x‖ < R → ∀ i j,
      A i j x = ((normalWaveMetric g q (normalWaveEquiv x))⁻¹ i j : ℂ))
    (hb : ∀ x, ‖normalWaveEquiv x‖ < R → ∀ j,
      b j x = (normalWaveFirstCoefficient g q (normalWaveEquiv x) j : ℂ))
    {x : Fin 3 → ℝ} (hx : normalWaveEquiv x ∈ e.source) (hxR : ‖normalWaveEquiv x‖ < R) :
    (fun y => complexLaplaceBeltrami g (normalChartWave e f) y + lam*normalChartWave e f y)
      =ᶠ[𝓝 (e (normalWaveEquiv x))] (fun y =>
        waveCoordinateOperator (fun i => Pi.single i 1) A b f (normalWaveEquiv.symm (e.symm y)) +
          lam*f (normalWaveEquiv.symm (e.symm y))) := by
  have ht := e.map_source hx
  have hcont := (e.continuousAt_symm ht).norm
  have hR : ∀ᶠ y in 𝓝 (e (normalWaveEquiv x)), ‖e.symm y‖ < R := by
    apply hcont.eventually (gt_mem_nhds _)
    simpa only [e.left_inv hx] using hxR
  filter_upwards [e.open_target.mem_nhds ht,hR] with y hy hyR
  let v := normalWaveEquiv.symm (e.symm y)
  have hv : normalWaveEquiv v ∈ e.source := by
    simpa only [v,ContinuousLinearEquiv.apply_symm_apply] using e.map_target hy
  have hvR : ‖normalWaveEquiv v‖ < R := by
    simpa only [v,ContinuousLinearEquiv.apply_symm_apply] using hyR
  have hey : e (normalWaveEquiv v) = y := by
    simp only [v,ContinuousLinearEquiv.apply_symm_apply,e.right_inv hy]
  have hL := normalChartWave_laplacian g q e he hf hc hs hi hv (hp _ hvR)
  have hE := normalWavePiOperator_eq_extension g q hf A b v (hA v hvR) (hb v hvR)
  have hval := normalChartWave_apply e f hv
  rw [hey] at hL hval
  rw [hL,hE,hval]
end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.normalChartWave_residual_germ_oai := @OAI.YauCounterexamples.normalChartWave_residual_germ_oai
