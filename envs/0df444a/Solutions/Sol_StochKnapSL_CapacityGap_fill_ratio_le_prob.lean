-- Prove2me | solution 1 for StochKnapSL.CapacityGap.fill_ratio_le_prob
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:41:46.075891+00:00
-- url     : https://prove2.me/submissions/54206acd-3404-46f3-8feb-a4171fa783b7

import Mathlib
import Definitions.Def_StochKnapSL_CapacityGap_Model
open MeasureTheory ProbabilityTheory
open StochKnapSL.CapacityGap

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (Δ : ℝ) (α : Fin N → ℝ)
    (hS : Standing μ d Δ α) (σ : Equiv.Perm (Fin N)) (Q : ℝ) (hQ : 0 ≤ Q) (i : Fin N) :
    (∫ ω, fill σ Q (fun j => d j ω) i ∂μ) / (∫ ω, d i ω ∂μ) ≤
      μ.real {ω | 0 < fill σ Q (fun j => d j ω) i} := by
  set S : Ω → ℝ := ∑ j ∈ ahead σ i, d j with hSdef
  have hSapp : ∀ ω, S ω = ∑ j ∈ ahead σ i, d j ω := fun ω => by simp [hSdef, Finset.sum_apply]
  have hSmeas : Measurable S := by
    have : S = fun ω => ∑ j ∈ ahead σ i, d j ω := funext hSapp
    rw [this]; exact Finset.measurable_sum _ (fun j _ => hS.meas j)
  set A : Set Ω := {ω | S ω < Q} with hA
  have hAm : MeasurableSet A := measurableSet_lt hSmeas measurable_const
  set g : ℝ → ℝ := (Set.Iio Q).indicator 1 with hg
  have hgm : Measurable g := measurable_const.indicator measurableSet_Iio
  have hni : i ∉ ahead σ i := by simp [ahead]
  have hind : IndepFun (g ∘ S) (id ∘ d i) μ :=
    (hS.indep.indepFun_finsetSum_of_notMem hS.meas hni).comp hgm measurable_id
  have hgS : ∀ ω, (g ∘ S) ω = A.indicator 1 ω := by
    intro ω; simp [hg, hA, Set.indicator, Set.mem_Iio]
  -- integrability of d i
  have hdi_int : Integrable (d i) μ := by
    refine Integrable.of_bound (C := Δ) (hS.meas i).aestronglyMeasurable ?_
    filter_upwards [hS.pos i, hS.bdd i] with ω h1 h2
    rw [Real.norm_eq_abs, abs_of_pos h1]; exact h2
  have hprod : ∫ ω, (g ∘ S) ω * d i ω ∂μ = μ.real A * ∫ ω, d i ω ∂μ := by
    have := hind.integral_fun_mul_eq_mul_integral
      (hgm.comp hSmeas).aestronglyMeasurable (hS.meas i).aestronglyMeasurable
    simp only [Function.comp_apply, id] at this ⊢
    rw [this]
    congr 1
    have : (fun ω => g (S ω)) = A.indicator 1 := funext hgS
    rw [this, integral_indicator_one hAm]
  -- pointwise bound fill ≤ (g ∘ S) * d i, fill ≥ 0 a.e.
  have hpt : ∀ ω, fill σ Q (fun j => d j ω) i ≤ (g ∘ S) ω * d i ω := by
    intro ω
    rw [hgS ω]
    unfold fill
    by_cases h : S ω < Q
    · simp only [Set.indicator, hA, Set.mem_setOf_eq, h, if_true, Pi.one_apply, one_mul]
      exact min_le_left _ _
    · simp only [Set.indicator, hA, Set.mem_setOf_eq, h, if_false, zero_mul]
      push_neg at h
      rw [← hSapp ω, max_eq_left (by linarith)]
      exact min_le_right _ _
  have hnn : 0 ≤ᵐ[μ] fun ω => fill σ Q (fun j => d j ω) i := by
    filter_upwards [hS.pos i] with ω h1
    exact le_min h1.le (le_max_left _ _)
  have hint2 : Integrable (fun ω => (g ∘ S) ω * d i ω) μ := by
    refine Integrable.bdd_mul (c := 1) hdi_int (hgm.comp hSmeas).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [hgS ω]; by_cases h : ω ∈ A <;> simp [Set.indicator, h]
  have hle : ∫ ω, fill σ Q (fun j => d j ω) i ∂μ ≤ μ.real A * ∫ ω, d i ω ∂μ := by
    rw [← hprod]
    exact integral_mono_of_nonneg hnn hint2 (Filter.Eventually.of_forall hpt)
  -- μ A ≤ μ {0 < fill}
  have hAle : μ.real A ≤ μ.real {ω | 0 < fill σ Q (fun j => d j ω) i} := by
    have hsub : A ∩ {ω | 0 < d i ω} ⊆ {ω | 0 < fill σ Q (fun j => d j ω) i} := by
      rintro ω ⟨h1, h2⟩
      simp only [hA, Set.mem_setOf_eq] at h1 h2 ⊢
      unfold fill
      apply lt_min h2
      rw [← hSapp ω]
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have heq : μ (A ∩ {ω | 0 < d i ω}) = μ A := by
      apply measure_inter_conull
      exact hS.pos i
    calc μ.real A = μ.real (A ∩ {ω | 0 < d i ω}) := by
          simp only [Measure.real, heq]
      _ ≤ _ := measureReal_mono hsub
  have hEnn : 0 ≤ ∫ ω, d i ω ∂μ :=
    integral_nonneg_of_ae (by filter_upwards [hS.pos i] with ω h; exact h.le)
  rcases hEnn.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; exact measureReal_nonneg
  · rw [div_le_iff₀ hpos]
    exact le_trans hle (mul_le_mul_of_nonneg_right hAle hpos.le)
