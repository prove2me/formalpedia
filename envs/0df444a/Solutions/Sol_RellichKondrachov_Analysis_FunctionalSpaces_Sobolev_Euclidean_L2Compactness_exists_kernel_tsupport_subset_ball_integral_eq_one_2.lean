-- Prove2me | solution 2 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.exists_kernel_tsupport_subset_ball_integral_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:38:13.706607+00:00
-- url     : https://prove2.me/submissions/7224b37b-ae81-4dec-8f9f-5643dd1e6816

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
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
theorem _root_.solution {deltaLoss : ℝ} (hδ : 0 < deltaLoss) :
    ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∫ x, ψ x ∂(volume : Measure E) = 1) ∧ tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss := by
  classical
  -- Start from a smooth bump supported in `ball 0 deltaLoss` with value `1` at `0`.
  have hs : (Metric.ball (0 : E) deltaLoss) ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hδ
  rcases exists_contDiff_tsupport_subset (n := ⊤)
    (E := E) (s := Metric.ball (0 : E) deltaLoss) (x := (0 : E)) hs with
    ⟨f, hf_tsupp, hf_cs, hf_smooth, hf_range, hf0⟩
  have hf_cont : Continuous f := hf_smooth.continuous
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    have hx : f x ∈ Set.Icc (0 : ℝ) 1 := hf_range ⟨x, rfl⟩
    exact hx.1
  have hf0_ne : f (0 : E) ≠ 0 := by
    -- `f 0 = 1`.
    simp [hf0]
  -- The integral is strictly positive (Lebesgue is an open-positive measure).
  have hIpos :
      0 < ∫ x, f x ∂(volume : Measure E) := by
    simpa using
      (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure E))
        hf_cont hf_cs hf_nonneg hf0_ne)
  set I : ℝ := ∫ x, f x ∂(volume : Measure E)
  have hI0 : I ≠ 0 := ne_of_gt hIpos
  have hIpos' : 0 < I := by simpa [I] using hIpos
  -- Normalize: `ψ = I⁻¹ • f`.
  let ψ : E → ℝ := fun x => I⁻¹ * f x
  have hψc : Continuous ψ := by
    exact (continuous_const.mul hf_cont)
  have hψcs : HasCompactSupport ψ := by
    exact
      (HasCompactSupport.smul_left (f := fun _x : E => I⁻¹) (f' := f) hf_cs)
  have hψ0 : ∀ x, 0 ≤ ψ x := by
    intro x
    have hInv : 0 ≤ I⁻¹ := by
      have : 0 ≤ I := le_of_lt hIpos'
      simpa using inv_nonneg.2 this
    simpa [ψ] using mul_nonneg hInv (hf_nonneg x)
  have hψint : ∫ x, ψ x ∂(volume : Measure E) = 1 := by
    have : (∫ x, ψ x ∂(volume : Measure E)) = I⁻¹ * I := by
      -- Pull out the constant scalar.
      simpa [ψ, I] using
        (MeasureTheory.integral_const_mul (μ := (volume : Measure E)) (r := I⁻¹) (f := f))
    simp [this, hI0]
  have hψ_tsupp : tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss := by
    -- Scaling does not enlarge topological support; use the bump support inclusion.
    have hsub : tsupport ψ ⊆ tsupport f := by
      simpa [ψ, smul_eq_mul] using (tsupport_smul_subset_right (f := fun _x : E => I⁻¹) (g := f))
    exact hsub.trans hf_tsupp
  exact ⟨ψ, hψc, hψcs, hψ0, hψint, hψ_tsupp⟩
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
