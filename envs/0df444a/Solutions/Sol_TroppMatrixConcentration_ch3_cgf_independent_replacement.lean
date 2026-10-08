-- Prove2me | solution 1 for TroppMatrixConcentration.ch3_cgf_independent_replacement
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:21:59.598415+00:00
-- url     : https://prove2.me/submissions/e0798117-8ebb-4624-9651-d0f7eae968e5

import Definitions.Def_TroppMatrixConcentration_probability
import Theorems.Thm_TroppMatrixConcentration_ch3_probabilistic_lieb
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
open TroppMatrixConcentration

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (H X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeasH : Measurable H) (hMeasX : Measurable X)
    (hHermH : ∀ᵐ ω ∂μ, (H ω).IsHermitian)
    (hHermX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hIndep : IndepFun H X μ)
    (hExpX : Integrable (fun ω => matrixExp (X ω)) μ)
    (hIntTotal : Integrable (fun ω => traceExp (H ω + X ω)) μ)
    (hIntReplaced : Integrable (fun ω =>
      traceExp (H ω + matrixLog (∫ u, matrixExp (X u) ∂μ))) μ) :
    (∫ ω, traceExp (H ω + X ω) ∂μ) ≤
      ∫ ω, traceExp (H ω + matrixLog (∫ u, matrixExp (X u) ∂μ)) ∂μ := by
  let M := Matrix (Fin d) (Fin d) ℂ
  let : NormedAlgebra ℚ M := NormedAlgebra.restrictScalars ℚ ℂ M
  have hc : Continuous (fun p : M × M => traceExp (p.1 + p.2)) := by
    dsimp [traceExp, matrixExp]
    fun_prop
  have hec : Continuous (fun A : M => matrixExp A) := by
    dsimp [matrixExp]
    fun_prop
  have hrc : Continuous (fun A : M =>
      traceExp (A + matrixLog (∫ u, matrixExp (X u) ∂μ))) := by
    dsimp [traceExp, matrixExp]
    fun_prop
  have hclosed : MeasurableSet {A : M | A.IsHermitian} := by
    exact (isClosed_eq continuous_star continuous_id).measurableSet
  have hmap := hIndep.map_prod_eq_prod_map_map hMeasH.aemeasurable hMeasX.aemeasurable
  have hp : Integrable (fun p : M × M => traceExp (p.1 + p.2))
      ((μ.map H).prod (μ.map X)) := by
    rw [← hmap]
    exact (integrable_map_measure hc.aestronglyMeasurable
      (hMeasH.prodMk hMeasX).aemeasurable).2 hIntTotal
  have hr : Integrable (fun A : M =>
      traceExp (A + matrixLog (∫ u, matrixExp (X u) ∂μ))) (μ.map H) :=
    (integrable_map_measure hrc.aestronglyMeasurable hMeasH.aemeasurable).2 hIntReplaced
  have he : Integrable (fun A : M => matrixExp A) (μ.map X) :=
    (integrable_map_measure hec.aestronglyMeasurable hMeasX.aemeasurable).2 hExpX
  have hmx : ∀ᵐ A ∂μ.map X, A.IsHermitian :=
    (ae_map_iff hMeasX.aemeasurable hclosed).2 hHermX
  have hmh : ∀ᵐ A ∂μ.map H, A.IsHermitian :=
    (ae_map_iff hMeasH.aemeasurable hclosed).2 hHermH
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hMeasX.aemeasurable
  calc
    (∫ ω, traceExp (H ω + X ω) ∂μ) =
        ∫ p : M × M, traceExp (p.1 + p.2) ∂((μ.map H).prod (μ.map X)) := by
      rw [← hmap, integral_map (hMeasH.prodMk hMeasX).aemeasurable hc.aestronglyMeasurable]
    _ = ∫ A : M, ∫ B : M, traceExp (A + B) ∂μ.map X ∂μ.map H := integral_prod _ hp
    _ ≤ ∫ A : M, traceExp (A + matrixLog (∫ u, matrixExp (X u) ∂μ)) ∂μ.map H := by
      apply integral_mono_ae hp.integral_prod_left hr
      filter_upwards [hmh] with A hA
      have h := ch3_probabilistic_lieb (μ.map X) A hA id measurable_id hmx he
      simpa only [id_eq, integral_map hMeasX.aemeasurable hec.aestronglyMeasurable] using h
    _ = _ := integral_map hMeasH.aemeasurable hrc.aestronglyMeasurable

