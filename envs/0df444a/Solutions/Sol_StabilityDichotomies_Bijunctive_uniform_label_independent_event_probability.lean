-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.uniform_label_independent_event_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:13:41.271741+00:00
-- url     : https://prove2.me/submissions/d0804158-97ea-4d58-862e-a3896316d380

import Mathlib
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function

theorem solution {Ω Δ ι : Type}
    [MeasurableSpace Ω] [MeasurableSpace Δ] [Fintype ι]
    (μ : Measure Ω) (ν : Measure Δ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (label : Ω → ι) (hlabel : ∀ i, MeasurableSet {ω | label ω = i})
    (huniform : ∀ i, μ.real {ω | label ω = i} = 1 / Fintype.card ι)
    (E : ι → Set Δ) (hE : ∀ i, MeasurableSet (E i)) :
    ((μ.prod ν) {z : Ω × Δ | z.2 ∈ E (label z.1)}).toReal =
      (1 / (Fintype.card ι : ℝ)) * ∑ i : ι, ν.real (E i) := by
  classical
  let A : ι → Set (Ω × Δ) := fun i => {ω | label ω = i} ×ˢ E i
  have hm (i : ι) : MeasurableSet (A i) := (hlabel i).prod (hE i)
  have hd : Pairwise (Disjoint on A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    have hi' : label z.1 = i := hi.1
    have hj' : label z.1 = j := hj.1
    exact hij (hi'.symm.trans hj')
  have hu : (⋃ i, A i) = {z : Ω × Δ | z.2 ∈ E (label z.1)} := by
    ext ⟨ω,δ⟩
    simp only [mem_iUnion,mem_setOf_eq]
    constructor
    · rintro ⟨i,hi⟩
      exact hi.1 ▸ hi.2
    · intro h
      exact ⟨label ω, rfl,h⟩
  have hs := measureReal_iUnion_fintype (μ := μ.prod ν) hd hm
  rw [hu] at hs
  change (μ.prod ν).real _ = _
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold Measure.real A
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  change μ.real {ω | label ω = i} * ν.real (E i) = _
  rw [huniform i]
  rfl

