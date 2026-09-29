-- Prove2me | solution 1 for VapnikChervonenkis.Inequality.eq11_permutation_average
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:15:04.009837+00:00
-- url     : https://prove2.me/submissions/1693bcd1-a457-47ce-a610-29d9436ea7dd

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Inequality

theorem aux_eq11_mp {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → X => x ∘ σ) (Measure.pi fun _ => P)
      (Measure.pi fun _ => P) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin n => P) σ.symm
  convert h using 1
  ext x i
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

theorem aux_eq11_main {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (n : ℕ) (p : (Fin n → X) → Prop) [DecidablePred p] (hA : MeasurableSet {x | p x}) :
    Measure.pi (fun _ : Fin n => P) {x | p x}
      = ENNReal.ofReal (∫ x, ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            p (x ∘ σ))).card : ℝ) / (n.factorial : ℝ)
          ∂(Measure.pi (fun _ : Fin n => P))) := by
  set μ := Measure.pi (fun _ : Fin n => P) with hμ
  set A : Set (Fin n → X) := {x | p x} with hAdef
  have hcard : ∀ x : Fin n → X, ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      p (x ∘ σ))).card : ℝ) = ∑ σ : Equiv.Perm (Fin n),
        ((fun x : Fin n → X => x ∘ σ) ⁻¹' A).indicator (1 : (Fin n → X) → ℝ) x := by
    intro x
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    by_cases h : p (x ∘ σ)
    · simp [h, Set.indicator_of_mem (show x ∈ (fun x : Fin n → X => x ∘ σ) ⁻¹' A from h)]
    · simp [h, Set.indicator_of_notMem (show x ∉ (fun x : Fin n → X => x ∘ σ) ⁻¹' A from h)]
  have hmeas : ∀ σ : Equiv.Perm (Fin n), MeasurableSet ((fun x : Fin n → X => x ∘ σ) ⁻¹' A) :=
    fun σ => (aux_eq11_mp P n σ).measurable hA
  have hint : ∀ σ : Equiv.Perm (Fin n),
      ∫ x, ((fun x : Fin n → X => x ∘ σ) ⁻¹' A).indicator (1 : (Fin n → X) → ℝ) x ∂μ = μ.real A := by
    intro σ
    rw [integral_indicator_one (hmeas σ)]
    simp only [Measure.real]
    rw [(aux_eq11_mp P n σ).measure_preimage hA.nullMeasurableSet]
  simp_rw [hcard]
  rw [integral_div, integral_finsetSum]
  · simp_rw [hint]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    have hf : ((n.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    rw [mul_div_cancel_left₀ _ hf, ofReal_measureReal]
  · intro σ _
    exact (integrable_const (1 : ℝ)).indicator (hmeas σ)

end VapnikChervonenkis.Inequality

open VapnikChervonenkis.Inequality
open MeasureTheory Filter Topology

theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hρ : ∀ l, Measurable (VapnikChervonenkis.Shared.semiSampleDeviation S l)) (ε : ℝ) (l : ℕ) :
    Measure.pi (fun _ : Fin (l + l) => P) {x | ε / 2 ≤ VapnikChervonenkis.Shared.semiSampleDeviation S l x}
      = ENNReal.ofReal (∫ x, ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) =>
            ε / 2 ≤ VapnikChervonenkis.Shared.semiSampleDeviation S l (x ∘ σ))).card : ℝ) / ((l + l).factorial : ℝ)
          ∂(Measure.pi (fun _ : Fin (l + l) => P))) :=
  aux_eq11_main P (l + l) (fun x => ε / 2 ≤ VapnikChervonenkis.Shared.semiSampleDeviation S l x)
    (hρ l measurableSet_Ici)
