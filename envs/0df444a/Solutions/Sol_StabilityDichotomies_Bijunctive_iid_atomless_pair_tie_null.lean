-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.iid_atomless_pair_tie_null
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:24:00.594522+00:00
-- url     : https://prove2.me/submissions/f56a70d5-4a62-4eb9-89d0-dea0867657fd

import Mathlib
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

private theorem iid_coordinate_threshold_tie_null (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    [NullSingletonClass μ₀] (n : ℕ) (i : Fin (n+1))
    (a : (Fin n → ℝ) → ℝ) (ha : Measurable a) :
    (Measure.pi (fun _ : Fin (n+1) => μ₀) {x | x i = a (i.removeNth x)}) = 0 := by
  let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ => μ₀)
  haveI : IsProbabilityMeasure ν := by unfold ν; infer_instance
  have hE : MeasurableSet {z : ℝ × (Fin n → ℝ) | z.1 = a z.2} :=
    measurableSet_eq_fun measurable_fst (ha.comp measurable_snd)
  have h : μ₀.prod ν {z : ℝ × (Fin n → ℝ) | z.1 = a z.2} = 0 := by
    rw [Measure.prod_apply_symm hE]
    simp
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hMP := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ₀) i
  have heq := hMP.measure_preimage_emb e.measurableEmbedding {z : ℝ × (Fin n → ℝ) | z.1 = a z.2}
  rw [h] at heq
  simpa [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply] using heq

theorem solution (n : ℕ) (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    [NullSingletonClass μ₀] (i j : Fin n) (hij : i ≠ j) :
    Measure.pi (fun _ : Fin n => μ₀) {x | x i = x j} = 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
    let a : (Fin n → ℝ) → ℝ := fun y => y k
    have ha : Measurable a := measurable_pi_apply k
    have h := iid_coordinate_threshold_tie_null μ₀ n i a ha
    convert h using 1
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    dsimp [a, Fin.removeNth]
    rw [hk]
