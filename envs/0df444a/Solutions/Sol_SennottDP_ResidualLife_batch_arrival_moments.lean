-- Prove2me | solution 1 for SennottDP.ResidualLife.batch_arrival_moments
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:18:16.040867+00:00
-- url     : https://prove2.me/submissions/e811a7ed-e0b5-4395-baf1-5fdf90bdd429

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist

set_option autoImplicit false

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace SennottDP.ResidualLife.BAM083

theorem lintegral_comp_nat {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℕ) (hY : Measurable Y) (f : ℕ → ℝ≥0∞) :
    ∫⁻ ω, f (Y ω) ∂P = ∑' j, f j * P (Y ⁻¹' {j}) := by
  rw [← lintegral_map (measurable_of_countable f) hY, lintegral_countable']
  congr 1 with j
  rw [Measure.map_apply hY (measurableSet_singleton j)]

end SennottDP.ResidualLife.BAM083

open MeasureTheory ProbabilityTheory SennottDP.ResidualLife ENNReal NNReal in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℕ → ℝ≥0∞) (X : ℕ → Ω → ℕ) (hXmeas : ∀ k, Measurable (X k))
    (hindep : iIndepFun X P) (hlaw : ∀ k j, P (X k ⁻¹' {j}) = p j)
    (hBA1 : moment p 2 < ∞) (s : ℕ) :
    ∫⁻ ω, (∑ k ∈ Finset.range s, (X k ω : ℝ≥0∞)) ∂P = moment p 1 * s ∧
    ∫⁻ ω, (∑ k ∈ Finset.range s, (X k ω : ℝ≥0∞)) ^ 2 ∂P =
      moment p 2 * s + moment p 1 ^ 2 * ((s * (s - 1) : ℕ) : ℝ≥0∞) := by
  have hm : ∀ k, Measurable (fun ω => (X k ω : ℝ≥0∞)) := fun k =>
    (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp (hXmeas k)
  have hE1 : ∀ k, ∫⁻ ω, (X k ω : ℝ≥0∞) ∂P = moment p 1 := by
    intro k
    rw [SennottDP.ResidualLife.BAM083.lintegral_comp_nat P (X k) (hXmeas k)
      (fun j => (j : ℝ≥0∞))]
    simp only [hlaw, SennottDP.ResidualLife.moment, pow_one]
  have hE2 : ∀ k, ∫⁻ ω, (X k ω : ℝ≥0∞) * (X k ω : ℝ≥0∞) ∂P = moment p 2 := by
    intro k
    rw [SennottDP.ResidualLife.BAM083.lintegral_comp_nat P (X k) (hXmeas k)
      (fun j => (j : ℝ≥0∞) * (j : ℝ≥0∞))]
    simp only [hlaw, SennottDP.ResidualLife.moment, sq]
  have hcross : ∀ k l, k ≠ l →
      ∫⁻ ω, (X k ω : ℝ≥0∞) * (X l ω : ℝ≥0∞) ∂P = moment p 1 ^ 2 := by
    intro k l h
    have hi : IndepFun (fun ω => (X k ω : ℝ≥0∞)) (fun ω => (X l ω : ℝ≥0∞)) P :=
      (hindep.indepFun h).comp (measurable_of_countable _) (measurable_of_countable _)
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (hm k).aemeasurable
      (hm l).aemeasurable hi, hE1, hE1, sq]
  have hmm : ∀ k l, Measurable (fun ω => (X k ω : ℝ≥0∞) * (X l ω : ℝ≥0∞)) :=
    fun k l => (hm k).mul (hm l)
  constructor
  · rw [lintegral_finset_sum _ (fun k _ => hm k)]
    simp only [hE1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [mul_comm]
  · simp_rw [sq, Finset.sum_mul_sum]
    rw [lintegral_finset_sum _ (fun k _ => Finset.measurable_sum _
      (fun l _ => hmm k l))]
    have hrow : ∀ k ∈ Finset.range s,
        ∫⁻ ω, ∑ l ∈ Finset.range s, (X k ω : ℝ≥0∞) * (X l ω : ℝ≥0∞) ∂P =
          moment p 2 + (s - 1 : ℕ) * moment p 1 ^ 2 := by
      intro k hk
      rw [lintegral_finset_sum _ (fun l _ => hmm k l),
        ← Finset.add_sum_erase _ _ hk, hE2]
      rw [Finset.sum_congr rfl (fun l hl => hcross k l (Finset.ne_of_mem_erase hl).symm),
        Finset.sum_const, Finset.card_erase_of_mem hk, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hrow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_mul]
    ring
