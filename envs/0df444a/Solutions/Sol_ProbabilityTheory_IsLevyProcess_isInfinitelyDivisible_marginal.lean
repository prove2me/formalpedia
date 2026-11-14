-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.isInfinitelyDivisible_marginal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:30:46.021626+00:00
-- url     : https://prove2.me/submissions/abceca0c-c65d-42a6-ae43-16d96a865ac0

import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_PoissonProcess
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.CharacteristicFunction
import Theorems.Thm_ProbabilityTheory_increment_apply
import Theorems.Thm_ProbabilityTheory_measurable_increment
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_indepFun_increment
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_identDistrib_increment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal Nat

universe u_2 u_3

theorem solution
    {Ω : Type u_2} [MeasurableSpace Ω]
    {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : ProbabilityTheory.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) :
    ProbabilityTheory.IsInfinitelyDivisible (μ.map (X t)) := by
  classical
  have hincr (v : ℝ≥0) : increment X 0 v = X v := by
    ext ω
    show X v ω - X 0 ω = X v ω
    rw [show X 0 ω = 0 from congr_fun h.start_zero ω, sub_zero]
  intro n hn
  set δ : ℝ≥0 := t / ↑n with hδ_def
  set ν := μ.map (X δ) with hν_def
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (hX δ).aemeasurable
  refine ⟨ν, inferInstance, ?_⟩
  have hn_ne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ht_eq : ↑n * δ = t := by
    rw [hδ_def]
    exact mul_div_cancel₀ t hn_ne
  rw [← ht_eq]
  suffices key : ∀ k : ℕ, μ.map (X (↑k * δ)) = ν.iteratedConv k from key n
  intro k
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, iteratedConv_zero]
    rw [h.start_zero, Measure.map_const, measure_univ, one_smul]
  | succ k ih =>
    have hcast : (↑(k + 1) : ℝ≥0) * δ = δ + ↑k * δ := by
      push_cast
      ring
    rw [hcast, iteratedConv_succ]
    have h_decomp : X (δ + ↑k * δ) = X δ + increment X δ (δ + ↑k * δ) := by
      ext ω
      simp only [Pi.add_apply, increment_apply]
      abel
    have h_indep : IndepFun (X δ) (increment X δ (δ + ↑k * δ)) μ := by
      have hh := h.indepFun_increment (s := 0) (t := δ) (u := δ + ↑k * δ)
        zero_le le_self_add
      rwa [hincr δ] at hh
    have hmI : AEMeasurable (increment X δ (δ + ↑k * δ)) μ :=
      (measurable_increment (hX _) (hX _)).aemeasurable
    have h_conv : μ.map (X (δ + ↑k * δ)) =
        μ.map (X δ) ∗ μ.map (increment X δ (δ + ↑k * δ)) := by
      rw [h_decomp]
      exact h_indep.map_add_eq_map_conv_map₀ (hX _).aemeasurable hmI
    have h_stat : μ.map (increment X δ (δ + ↑k * δ)) =
        μ.map (X (↑k * δ)) := by
      have hid := h.identDistrib_increment δ (↑k * δ)
      rw [hid.map_eq, hincr (↑k * δ)]
    rw [h_conv, h_stat, ih]
