-- Prove2me | solution 1 for ZORiem.RGD.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T13:10:13.275339+00:00
-- url     : https://prove2.me/submissions/4e5249c3-c1d1-4acb-b526-7d46665949eb

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (X : Submodule ℝ E) (d : ℕ)
    (hd : Module.finrank ℝ X = d) (x : E) (hx : x ∈ X) :
    Integrable (fun u₀ : E => ⟪x, X.starProjection u₀⟫_ℝ • X.starProjection u₀) (stdGaussian E) ∧
    ∫ u₀, ⟪x, X.starProjection u₀⟫_ℝ • X.starProjection u₀ ∂(stdGaussian E) = x ∧
    ∫ u₀, ⟪x, X.starProjection u₀⟫_ℝ ^ 2 ∂(stdGaussian E) = ‖x‖ ^ 2 := by
  haveI htriple : ENNReal.HolderTriple 2 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  have hμ : MemLp (id : E → E) 2 (stdGaussian E) := IsGaussian.memLp_two_id
  -- The second moment identity for the standard Gaussian measure.
  have hmoment : ∀ a b : E, ∫ u, ⟪a, u⟫_ℝ * ⟪b, u⟫_ℝ ∂(stdGaussian E) = ⟪a, b⟫_ℝ := by
    intro a b
    have hcov := covarianceBilin_apply (μ := stdGaussian E) hμ a b
    rw [covarianceBilin_stdGaussian] at hcov
    have hzero : (∫ x : E, id x ∂(stdGaussian E)) = 0 := by simp
    rw [hzero] at hcov
    rw [innerSL_apply_apply] at hcov
    simpa using hcov.symm
  -- For `w ∈ X`, the projection is invisible in the left slot.
  have hinner_left : ∀ w ∈ X, ∀ u : E, ⟪w, X.starProjection u⟫_ℝ = ⟪w, u⟫_ℝ := by
    intro w hw u
    have h0 : ⟪w, u - X.starProjection u⟫_ℝ = 0 := by
      rw [real_inner_comm]
      exact Submodule.starProjection_inner_eq_zero (K := X) u w hw
    have h1 : ⟪w, u⟫_ℝ = ⟪w, X.starProjection u⟫_ℝ := by
      have h := h0
      rw [inner_sub_right] at h
      exact sub_eq_zero.mp h
    exact h1.symm
  -- General rearrangement: `⟪y, P u⟫ = ⟪P y, u⟫`.
  have hinner_gen : ∀ y u : E, ⟪y, X.starProjection u⟫_ℝ = ⟪X.starProjection y, u⟫_ℝ := by
    intro y u
    have h0 : ⟪y - X.starProjection y, X.starProjection u⟫_ℝ = 0 :=
      Submodule.starProjection_inner_eq_zero (K := X) y (X.starProjection u)
        (Submodule.starProjection_apply_mem X u)
    have h1 : ⟪y, X.starProjection u⟫_ℝ = ⟪X.starProjection y, X.starProjection u⟫_ℝ := by
      have h := h0
      rw [inner_sub_left] at h
      exact sub_eq_zero.mp h
    rw [h1]
    exact hinner_left (X.starProjection y) (Submodule.starProjection_apply_mem X y) u
  -- Key mixed moment identity for the projected Gaussian.
  have hkey : ∀ y : E,
      ∫ u, ⟪x, X.starProjection u⟫_ℝ * ⟪y, X.starProjection u⟫_ℝ ∂(stdGaussian E) = ⟪x, y⟫_ℝ := by
    intro y
    have h1 : (fun u : E => ⟪x, X.starProjection u⟫_ℝ * ⟪y, X.starProjection u⟫_ℝ)
        = (fun u : E => ⟪x, u⟫_ℝ * ⟪X.starProjection y, u⟫_ℝ) := by
      funext u
      rw [hinner_left x hx u, hinner_gen y u]
    rw [h1, hmoment x (X.starProjection y), hinner_left x hx y]
  -- Membership in `L²` of the relevant functions.
  have hP_memLp : MemLp (fun u : E => X.starProjection u) 2 (stdGaussian E) := by
    simpa using X.starProjection.comp_memLp' hμ
  have hφ : MemLp (fun u : E => ⟪x, X.starProjection u⟫_ℝ) 2 (stdGaussian E) :=
    hP_memLp.const_inner x
  have hf_int : Integrable
      (fun u : E => ⟪x, X.starProjection u⟫_ℝ • X.starProjection u) (stdGaussian E) := by
    rw [← memLp_one_iff_integrable]
    exact hP_memLp.smul hφ
  have hsq_int : Integrable (fun u : E => ⟪x, X.starProjection u⟫_ℝ ^ 2) (stdGaussian E) :=
    hφ.integrable_sq
  -- The scalar second moment.
  have hsq : ∫ u, ⟪x, X.starProjection u⟫_ℝ ^ 2 ∂(stdGaussian E) = ‖x‖ ^ 2 := by
    rw [show (fun u : E => ⟪x, X.starProjection u⟫_ℝ ^ 2)
        = (fun u : E => ⟪x, X.starProjection u⟫_ℝ * ⟪x, X.starProjection u⟫_ℝ) from by
          funext u; exact pow_two _]
    rw [hkey x, real_inner_self_eq_norm_sq]
  refine ⟨hf_int, ?_, hsq⟩
  -- The vector integral, via the inner product characterization.
  have hg_int : Integrable
      (fun u : E => ⟪x, X.starProjection u⟫_ℝ • X.starProjection u - x) (stdGaussian E) :=
    hf_int.sub (integrable_const x)
  have hzero : ∫ u, (⟪x, X.starProjection u⟫_ℝ • X.starProjection u - x) ∂(stdGaussian E) = 0 := by
    refine integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ hg_int ?_
    intro c
    have h1 : Integrable
        (fun u : E => ⟪x, X.starProjection u⟫_ℝ * ⟪c, X.starProjection u⟫_ℝ)
        (stdGaussian E) := by
      rw [← memLp_one_iff_integrable]
      exact (hP_memLp.const_inner c).mul hφ
    have h2 : (fun u : E => ⟪c, (⟪x, X.starProjection u⟫_ℝ • X.starProjection u - x)⟫_ℝ)
        = (fun u : E => ⟪x, X.starProjection u⟫_ℝ * ⟪c, X.starProjection u⟫_ℝ - ⟪c, x⟫_ℝ) := by
      funext u
      rw [inner_sub_right, inner_smul_right]
    rw [h2, integral_sub h1 (integrable_const _), hkey c, integral_const]
    simp [real_inner_comm]
  rw [integral_sub hf_int (integrable_const x), integral_const] at hzero
  exact sub_eq_zero.mp (by simpa using hzero)
