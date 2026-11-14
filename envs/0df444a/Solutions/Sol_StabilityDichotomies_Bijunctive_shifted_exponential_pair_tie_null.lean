-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.shifted_exponential_pair_tie_null
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:27:24.686371+00:00
-- url     : https://prove2.me/submissions/0bf909df-dec4-4525-bac9-870dd62e6a20

import Theorems.Thm_StabilityDichotomies_Bijunctive_independent_exponential_threshold_tie_null
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Bijunctive

private theorem coordinate_threshold_tie_null (n : ℕ) (i : Fin (n+1))
    (a : (Fin n → ℝ) → ℝ) (ha : Measurable a) (β : ℝ) (hβ : 0 < β) :
    (Measure.pi (fun _ : Fin (n+1) => expMeasure β)
      {δ | δ i = a (i.removeNth δ)}) = 0 := by
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ => expMeasure β)
  haveI : IsProbabilityMeasure ν := by unfold ν; infer_instance
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hMP := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => expMeasure β) i
  have h := independent_exponential_threshold_tie_null ν a ha β hβ
  have heq := hMP.measure_preimage_emb e.measurableEmbedding {z : ℝ × (Fin n → ℝ) | z.1 = a z.2}
  rw [h] at heq
  simpa [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply] using heq

theorem solution (q : ℕ) (β : ℝ) (hβ : 0 < β)
    (d : Fin q → ℝ) (i j : Fin q) (hij : i ≠ j) :
    (Measure.pi (fun _ : Fin q => expMeasure β) {δ | δ i - d i = δ j - d j}) = 0 := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ n =>
    obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
    let a : (Fin n → ℝ) → ℝ := fun y => y k + d i - d j
    have ha : Measurable a := by unfold a; fun_prop
    have h := coordinate_threshold_tie_null n i a ha β hβ
    convert h using 1
    congr 1
    ext δ
    simp only [Set.mem_setOf_eq]
    dsimp [a, Fin.removeNth]
    rw [hk]
    constructor <;> intro h <;> linarith
