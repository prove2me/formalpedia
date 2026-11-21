-- Prove2me | solution 1 for ProphetBipartite.fact_3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:23:39.485422+00:00
-- url     : https://prove2.me/submissions/ecc637a1-e84a-4056-8f0e-df728ab6a251

import Mathlib
import Definitions.Def_ProphetBipartite_IsOptSelector
import Definitions.Def_ProphetBipartite_Mmat

open MeasureTheory
open scoped NNReal

namespace Aux_PB32

theorem meas_set {E : Type*} [Fintype E] [DecidableEq E] (opt : (E → ℝ≥0) → Finset E)
    (hmeas : ∀ S : Finset E, MeasurableSet {v : E → ℝ≥0 | opt v = S}) (P : E → Prop) :
    MeasurableSet {v : E → ℝ≥0 | ∃ e ∈ opt v, P e} := by
  have h : {v : E → ℝ≥0 | ∃ e ∈ opt v, P e} =
      ⋃ S : Finset E, ({v : E → ℝ≥0 | opt v = S} ∩ {_v | ∃ e ∈ S, P e}) := by
    ext v
    simp
  rw [h]
  exact MeasurableSet.iUnion (fun S => (hmeas S).inter (MeasurableSet.const _))

theorem sum_le_one {ι Ω : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Function.onFun Disjoint A)) :
    ∑ i, P.real (A i) ≤ 1 := by
  rw [← measureReal_iUnion_fintype hd hA (fun i => measure_ne_top _ _)]
  exact measureReal_le_one

end Aux_PB32

open ProphetBipartite Aux_PB32 in
theorem solution {L R E : Type*} [Fintype L] [Fintype R] [Fintype E] [DecidableEq E]
    (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (opt : (E → ℝ≥0) → Finset E) (hopt : IsOptSelector left right opt) :
    (∀ i, ∑ j, Qmat left right opt μ i j ≤ 1) ∧ ∀ j, ∑ i, Qmat left right opt μ i j ≤ 1 := by
  constructor
  · intro i
    show ∑ j, (Measure.pi μ).real {v | ∃ e ∈ opt v, left e = i ∧ right e = j} ≤ 1
    apply sum_le_one
    · intro j
      exact meas_set opt hopt.2 (fun e => left e = i ∧ right e = j)
    · intro j j' hjj'
      refine Set.disjoint_left.2 ?_
      rintro v ⟨e, he, hl, hr⟩ ⟨e', he', hl', hr'⟩
      by_cases hee : e = e'
      · subst hee
        exact hjj' (hr.symm.trans hr')
      · exact ((hopt.1 v).1 e he e' he' hee).1 (hl.trans hl'.symm)
  · intro j
    show ∑ i, (Measure.pi μ).real {v | ∃ e ∈ opt v, left e = i ∧ right e = j} ≤ 1
    apply sum_le_one
    · intro i
      exact meas_set opt hopt.2 (fun e => left e = i ∧ right e = j)
    · intro i i' hii'
      refine Set.disjoint_left.2 ?_
      rintro v ⟨e, he, hl, hr⟩ ⟨e', he', hl', hr'⟩
      by_cases hee : e = e'
      · subst hee
        exact hii' (hl.symm.trans hl')
      · exact ((hopt.1 v).1 e he e' he' hee).2 (hr.trans hr'.symm)
