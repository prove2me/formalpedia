-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.finite_almost_sure_partition_independent_event_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:14:58.335976+00:00
-- url     : https://prove2.me/submissions/f896c279-c807-4a5b-90a7-334c5d1463de

import Mathlib
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function

theorem solution {Ω Δ ι : Type}
    [MeasurableSpace Ω] [MeasurableSpace Δ] [Fintype ι]
    (μ : Measure Ω) (ν : Measure Δ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : ι → Set Ω) (hP : ∀ i, MeasurableSet (P i)) (hdis : Pairwise (Disjoint on P))
    (hcover : ∀ᵐ ω ∂μ, ∃ i, ω ∈ P i)
    (E : ι → Set Δ) (hE : ∀ i, MeasurableSet (E i)) (T : Set (Ω × Δ))
    (hsection : ∀ i ω δ, ω ∈ P i → ((ω,δ) ∈ T ↔ δ ∈ E i)) :
    ((μ.prod ν) T).toReal = ∑ i : ι, μ.real (P i) * ν.real (E i) := by
  classical
  let A : ι → Set (Ω × Δ) := fun i => P i ×ˢ E i
  have hm (i : ι) : MeasurableSet (A i) := (hP i).prod (hE i)
  have hd : Pairwise (Disjoint on A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact (Set.disjoint_left.mp (hdis hij)) hi.1 hj.1
  have hcover' : ∀ᵐ z ∂(μ.prod ν), ∃ i, z.1 ∈ P i :=
    measurePreserving_fst.quasiMeasurePreserving.ae hcover
  have hEq : T =ᵐ[μ.prod ν] ⋃ i, A i := by
    filter_upwards [hcover'] with z ⟨i,hi⟩
    apply propext
    constructor
    · intro hz
      exact Set.mem_iUnion.mpr ⟨i,hi,(hsection i z.1 z.2 hi).mp hz⟩
    · intro hz
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
      exact (hsection j z.1 z.2 hj.1).mpr hj.2
  have hs := measureReal_iUnion_fintype (μ := μ.prod ν) hd hm
  change (μ.prod ν).real T = _
  rw [Measure.real, measure_congr hEq]
  change (μ.prod ν).real (⋃ i, A i) = _
  rw [hs]
  apply Finset.sum_congr rfl
  intro i hi
  unfold Measure.real A
  rw [Measure.prod_prod,ENNReal.toReal_mul]
