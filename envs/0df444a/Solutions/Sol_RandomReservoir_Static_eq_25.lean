-- Prove2me | solution 1 for RandomReservoir.Static.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:16:46.325203+00:00
-- url     : https://prove2.me/submissions/1b3d429e-9a95-4166-b3f5-49cdbe01a1d8

import Mathlib
import Definitions.Def_RandomReservoir_Static_Setting

open MeasureTheory ProbabilityTheory

open RandomReservoir.Static in
theorem solution
    {𝒳 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [CompleteSpace 𝒳]
    [TopologicalSpace.SeparableSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (N : ℕ) (hN : 0 < N)
    (π : Measure (𝒳 × ℝ)) [IsProbabilityMeasure π]
    (φ : 𝒳 × ℝ → ℝ) (hφ : Measurable φ) (z : 𝒳) (c : ℝ)
    (hL2 : MemLp (fun p : 𝒳 × ℝ => φ p * relu (inner ℝ p.1 z + p.2)) 2 π)
    (hc : ∫ p, φ p * relu (inner ℝ p.1 z + p.2) ∂π = c) :
    ∫ θ, ((1 / (N : ℝ)) * ∑ i, φ (θ i) * relu (inner ℝ (θ i).1 z + (θ i).2) - c) ^ 2
        ∂(Measure.pi fun _ : Fin N => π)
      = (1 / (N : ℝ)) * variance (fun p : 𝒳 × ℝ => φ p * relu (inner ℝ p.1 z + p.2)) π ∧
    (1 / (N : ℝ)) * variance (fun p : 𝒳 × ℝ => φ p * relu (inner ℝ p.1 z + p.2)) π
      ≤ (1 / (N : ℝ)) * ∫ p, φ p ^ 2 * relu (inner ℝ p.1 z + p.2) ^ 2 ∂π := by
  set f : 𝒳 × ℝ → ℝ := fun p => φ p * relu (inner ℝ p.1 z + p.2) with hf
  set P := Measure.pi fun _ : Fin N => π with hP
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hYm : ∀ i : Fin N, MemLp (fun θ : Fin N → 𝒳 × ℝ => f (θ i)) 2 P :=
    fun i => hL2.comp_measurePreserving (measurePreserving_eval _ i)
  have hsumvar : variance (∑ i : Fin N, fun θ : Fin N → 𝒳 × ℝ => f (θ i)) P =
      N * variance f π := by
    rw [hP, variance_sum_pi (X := fun _ => f) (fun _ => hL2)]
    simp
  have hsumfun : (∑ i : Fin N, fun θ : Fin N → 𝒳 × ℝ => f (θ i)) =
      fun θ => ∑ i, f (θ i) := by
    funext θ
    simp [Finset.sum_apply]
  have hS : MemLp (fun θ : Fin N → 𝒳 × ℝ => ∑ i, f (θ i)) 2 P := by
    rw [← hsumfun]
    exact memLp_finset_sum' _ (fun i _ => hYm i)
  have hint_i : ∀ i : Fin N, ∫ θ, f (θ i) ∂P = c := by
    intro i
    have hmp := measurePreserving_eval (fun _ : Fin N => π) i
    have := integral_map (μ := P) hmp.measurable.aemeasurable (f := f)
      (by rw [hmp.map_eq]; exact hL2.aestronglyMeasurable)
    rw [hmp.map_eq] at this
    rw [← hc]
    exact this.symm
  have hmean : ∫ θ, (1 / (N : ℝ)) * ∑ i, f (θ i) ∂P = c := by
    rw [integral_const_mul, integral_finset_sum _ (fun i _ => (hYm i).integrable one_le_two)]
    simp only [hint_i, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hvar_avg : variance (fun θ : Fin N → 𝒳 × ℝ => (1 / (N : ℝ)) * ∑ i, f (θ i)) P =
      (1 / (N : ℝ)) ^ 2 * (N * variance f π) := by
    rw [variance_const_mul, ← hsumvar, hsumfun]
  constructor
  · have hae : AEMeasurable (fun θ : Fin N → 𝒳 × ℝ => (1 / (N : ℝ)) * ∑ i, f (θ i)) P :=
      (hS.const_mul (1 / (N : ℝ))).aestronglyMeasurable.aemeasurable
    have := variance_eq_integral hae
    rw [hmean] at this
    rw [← this, hvar_avg]
    field_simp
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc variance f π ≤ π[f ^ 2] := variance_le_expectation_sq hL2.aestronglyMeasurable
      _ = ∫ p, φ p ^ 2 * relu (inner ℝ p.1 z + p.2) ^ 2 ∂π := by
          congr 1
          funext p
          simp only [hf, Pi.pow_apply, mul_pow]
