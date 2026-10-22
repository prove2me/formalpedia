-- Prove2me | solution 1 for RelSmoothFOM.DualAvg.eq_35
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:58:32.091011+00:00
-- url     : https://prove2.me/submissions/54ace2ec-f464-4140-a457-12b0bec754a4

import Mathlib
import Definitions.Def_RelSmoothFOM_DualAvg_Setting

set_option autoImplicit false
open RelSmoothFOM.DualAvg

theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hμ : 0 ≤ μ) (hμL : μ < L)
    (x : ℕ → E) (hrun : IsDualAveragingRun Q f h L μ x) :
    ∀ k : ℕ, ∀ u ∈ Q,
      (1 + μ * daSum L μ k) * bregman h u (x k) = bregman (daModel f h L μ x k) u (x k) ∧
      bregman (daModel f h L μ x k) u (x k) ≤
        daModel f h L μ x k u - daModel f h L μ x k (x k) := by
  intro k u hu
  have hxk : x k ∈ Q := by
    cases k with
    | zero => exact hrun.1
    | succ k => exact (hrun.2.2.2 k).1
  have hdh : DifferentiableAt ℝ h (x k) := hhd _ hxk
  have hmin : IsMinOn (daModel f h L μ x k) Q (x k) := by
    cases k with
    | zero =>
      intro w hw
      have := hrun.2.2.1 w hw
      simpa [daModel] using this
    | succ k => exact fun w hw => (hrun.2.2.2 k).2 w hw
  set G : E →L[ℝ] ℝ := fderiv ℝ h (x k) + ∑ i ∈ Finset.range k, daWeight L μ i •
        (fderiv ℝ f (x i) + μ • (fderiv ℝ h (x k) - fderiv ℝ h (x i))) with hG
  have hψ : HasFDerivAt (daModel f h L μ x k) G (x k) := by
    unfold daModel
    simp only [bregman]
    refine hdh.hasFDerivAt.add ?_
    apply HasFDerivAt.fun_sum
    intro i _
    have h1 : HasFDerivAt (fun w : E => fderiv ℝ f (x i) (w - x i)) (fderiv ℝ f (x i)) (x k) := by
      have := ((fderiv ℝ f (x i)).hasFDerivAt (x := x k)).sub_const (fderiv ℝ f (x i) (x i))
      exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp [map_sub])
    have h2 : HasFDerivAt (fun w : E => fderiv ℝ h (x i) (w - x i)) (fderiv ℝ h (x i)) (x k) := by
      have := ((fderiv ℝ h (x i)).hasFDerivAt (x := x k)).sub_const (fderiv ℝ h (x i) (x i))
      exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp [map_sub])
    have := (((hasFDerivAt_const (f (x i)) (x k)).add h1).add
      (((hdh.hasFDerivAt.sub_const (h (x i))).sub h2).const_mul μ)).const_mul (daWeight L μ i)
    refine HasFDerivAt.congr_of_eventuallyEq (this.congr_fderiv ?_)
      (Filter.Eventually.of_forall fun y => ?_)
    · simp
    · simp only [Pi.add_apply, Pi.sub_apply]
  have hnn : 0 ≤ G (u - x k) :=
    hmin.localize.hasFDerivWithinAt_nonneg hψ.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset (hQ.segment_subset hxk hu))
  have hbreg : bregman (daModel f h L μ x k) u (x k) =
      daModel f h L μ x k u - daModel f h L μ x k (x k) - G (u - x k) := by
    unfold bregman
    rw [hψ.fderiv]
  refine ⟨?_, ?_⟩
  · rw [hbreg]
    have hGe : G (u - x k) = fderiv ℝ h (x k) (u - x k) + ∑ i ∈ Finset.range k, daWeight L μ i *
        (fderiv ℝ f (x i) (u - x k) + μ * (fderiv ℝ h (x k) (u - x k) - fderiv ℝ h (x i) (u - x k))) := by
      simp only [hG, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]
    have hterm : ∀ i ∈ Finset.range k,
        daWeight L μ i * (f (x i) + fderiv ℝ f (x i) (u - x i) + μ * bregman h u (x i)) -
          daWeight L μ i * (f (x i) + fderiv ℝ f (x i) (x k - x i) + μ * bregman h (x k) (x i)) -
          daWeight L μ i * (fderiv ℝ f (x i) (u - x k) +
            μ * (fderiv ℝ h (x k) (u - x k) - fderiv ℝ h (x i) (u - x k))) =
        daWeight L μ i * μ * bregman h u (x k) := by
      intro i _
      unfold bregman
      simp only [map_sub]
      ring
    have hsum : ∑ i ∈ Finset.range k, daWeight L μ i * (f (x i) + fderiv ℝ f (x i) (u - x i) +
          μ * bregman h u (x i)) -
        ∑ i ∈ Finset.range k, daWeight L μ i * (f (x i) + fderiv ℝ f (x i) (x k - x i) +
          μ * bregman h (x k) (x i)) -
        ∑ i ∈ Finset.range k, daWeight L μ i *
          (fderiv ℝ f (x i) (u - x k) + μ * (fderiv ℝ h (x k) (u - x k) - fderiv ℝ h (x i) (u - x k))) =
        μ * daSum L μ k * bregman h u (x k) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm]
      unfold daSum
      rw [mul_comm μ, Finset.sum_mul, Finset.sum_mul]
    have hBh : bregman h u (x k) = h u - h (x k) - fderiv ℝ h (x k) (u - x k) := rfl
    have hu1 : daModel f h L μ x k u = h u + ∑ i ∈ Finset.range k, daWeight L μ i *
        (f (x i) + fderiv ℝ f (x i) (u - x i) + μ * bregman h u (x i)) := rfl
    have hu2 : daModel f h L μ x k (x k) = h (x k) + ∑ i ∈ Finset.range k, daWeight L μ i *
        (f (x i) + fderiv ℝ f (x i) (x k - x i) + μ * bregman h (x k) (x i)) := rfl
    rw [hGe, hu1, hu2]
    rw [hBh] at hsum ⊢
    linarith
  · rw [hbreg]
    linarith
