-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.exists_kernel_tsupport_subset_ball_integral_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:10:56.431195+00:00
-- url     : https://prove2.me/submissions/abbeaf0a-34c2-4526-bc74-5973e4fe4985

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceEL2CompactnessKernels
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceEL2CompactnessKernels
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpaceEL2CompactnessKernels

theorem solution {deltaLoss : ℝ} (hδ : 0 < deltaLoss) :
    ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∫ x, ψ x ∂(volume : Measure E) = 1) ∧ tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss := by
  classical
  have hs : (Metric.ball (0 : E) deltaLoss) ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hδ
  rcases exists_contDiff_tsupport_subset (n := ⊤)
    (E := E) (s := Metric.ball (0 : E) deltaLoss) (x := (0 : E)) hs with
    ⟨f, hf_tsupp, hf_cs, hf_smooth, hf_range, hf0⟩
  have hf_cont : Continuous f := hf_smooth.continuous
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact (hf_range ⟨x, rfl⟩).1
  have hf_int : Integrable f (volume : Measure E) :=
    hf_cont.integrable_of_hasCompactSupport hf_cs
  let I : ℝ := ∫ x, f x ∂(volume : Measure E)
  have hI0 : 0 < I := by
    exact hf_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : E))
      hf_cs hf_nonneg (by simp [hf0])
  let ψ : E → ℝ := fun x => I⁻¹ * f x
  have hψc : Continuous ψ := by
    exact continuous_const.mul hf_cont
  have hψcs : HasCompactSupport ψ := by
    exact
      (HasCompactSupport.smul_left (f := fun _x : E => I⁻¹) (f' := f) hf_cs)
  have hψ0 : ∀ x, 0 ≤ ψ x := by
    intro x
    exact mul_nonneg (inv_nonneg.mpr hI0.le) (hf_nonneg x)
  have hψint : (∫ x, ψ x ∂(volume : Measure E)) = 1 := by
    have this : (∫ x, ψ x ∂(volume : Measure E)) =
        I⁻¹ * ∫ x, f x ∂(volume : Measure E) := by
      simpa [ψ, I] using
        (MeasureTheory.integral_const_mul (μ := (volume : Measure E)) (r := I⁻¹) (f := f))
    simp [this, I, hI0.ne']
  have hψ_tsupp : tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss := by
    have hsub : tsupport ψ ⊆ tsupport f := by
      simpa [ψ, smul_eq_mul] using (tsupport_smul_subset_right (f := fun _x : E => I⁻¹) (g := f))
    exact hsub.trans hf_tsupp
  exact ⟨ψ, hψc, hψcs, hψ0, hψint, hψ_tsupp⟩
