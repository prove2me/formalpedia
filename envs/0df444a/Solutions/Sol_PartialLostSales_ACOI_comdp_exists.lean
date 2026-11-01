-- Prove2me | solution 1 for PartialLostSales.ACOI.comdp_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:04:49.561987+00:00
-- url     : https://prove2.me/submissions/2de153c7-d0cb-4a43-a08b-e0043c381a5e

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE Set
open scoped ENNReal NNReal

open PartialLostSales.ACOI in
theorem solution (P : Params) (hP : Standing P) :
    ∃ M : MDP (Bel P) (Act P), IsCOMDP P M := by
  obtain ⟨hK, hhp, hhm, hprob, hac, hint, hmean, hvar, hneg⟩ := hP
  haveI := hprob
  -- the kernel `p ↦ z` on `Bel P × Act P`
  have hz : Measurable (fun p : Bel P × Act P => ((p.1 : ProbabilityMeasure ℝ≥0) : Measure ℝ≥0)) :=
    measurable_subtype_coe.comp (measurable_subtype_coe.comp measurable_fst)
  let κ : Kernel (Bel P × Act P) ℝ≥0 := ⟨fun p => ((p.1 : ProbabilityMeasure ℝ≥0) : Measure ℝ≥0), hz⟩
  haveI : IsMarkovKernel κ := ⟨fun p => by
    show IsProbabilityMeasure ((p.1 : ProbabilityMeasure ℝ≥0) : Measure ℝ≥0); infer_instance⟩
  -- measurability of the next-inventory law
  let g : (Bel P × Act P) → ℝ≥0 × ℝ → ℝ≥0 := fun p q => Real.toNNReal ((q.1 : ℝ) + (p.2 : ℝ) - q.2)
  have hg : Measurable (Function.uncurry g) := by
    unfold g; fun_prop
  have hnext : Measurable (fun p : Bel P × Act P => nextLaw P p.1.1 p.2) := by
    refine Measure.measurable_of_measurable_coe _ (fun S hS => ?_)
    have : ∀ p : Bel P × Act P, nextLaw P p.1.1 p.2 S =
        ∫⁻ x, P.demand (Prod.mk (p, x) ⁻¹' {q : ((Bel P × Act P) × ℝ≥0) × ℝ |
          g q.1.1 (q.1.2, q.2) ∈ S}) ∂(κ p) := by
      intro p
      have hgp : Measurable (g p) := hg.comp measurable_prodMk_left
      unfold nextLaw
      rw [Measure.map_apply hgp hS, Measure.prod_apply (hgp hS)]
      rfl
    simp_rw [this]
    refine Measurable.lintegral_kernel_prod_right (f := fun p x => P.demand (Prod.mk (p, x) ⁻¹'
      {q : ((Bel P × Act P) × ℝ≥0) × ℝ | g q.1.1 (q.1.2, q.2) ∈ S})) ?_
    have hT : MeasurableSet {q : ((Bel P × Act P) × ℝ≥0) × ℝ | g q.1.1 (q.1.2, q.2) ∈ S} :=
      (hg.comp (by fun_prop : Measurable fun q : ((Bel P × Act P) × ℝ≥0) × ℝ =>
        (q.1.1, (q.1.2, q.2)))) hS
    exact measurable_measure_prodMk_left hT
  have hR0 : Measurable (fun p : Bel P × Act P => R0 P p.1.1 p.2) :=
    (Measure.measurable_coe (measurableSet_singleton 0)).comp hnext
  have hR1 : Measurable (fun p : Bel P × Act P => R1 P p.1.1 p.2) :=
    (Measure.measurable_coe measurableSet_Ioi).comp hnext
  -- measurability of the posterior
  have hpost : Measurable (fun p : Bel P × Act P => post P p.1.1 p.2) := by
    have hset : MeasurableSet {p : Bel P × Act P |
        nextLaw P p.1.1 p.2 (Ioi 0) ≠ 0 ∧ nextLaw P p.1.1 p.2 (Ioi 0) ≠ ⊤} :=
      (hR1 (measurableSet_singleton 0).compl).inter (hR1 (measurableSet_singleton ⊤).compl)
    have hc : Measurable (fun p : Bel P × Act P =>
        (nextLaw P p.1.1 p.2 (Ioi 0))⁻¹ • (nextLaw P p.1.1 p.2).restrict (Ioi 0)) := by
      refine Measure.measurable_of_measurable_coe _ (fun S hS => ?_)
      simp only [Measure.smul_apply, Measure.restrict_apply hS, smul_eq_mul]
      exact hR1.inv.mul ((Measure.measurable_coe (hS.inter measurableSet_Ioi)).comp hnext)
    have hpos : ∀ x : {p : Bel P × Act P |
        nextLaw P p.1.1 p.2 (Ioi 0) ≠ 0 ∧ nextLaw P p.1.1 p.2 (Ioi 0) ≠ ⊤},
        post P x.1.1.1 x.1.2 = ⟨ProbabilityTheory.cond (nextLaw P x.1.1.1 x.1.2) (Ioi 0),
          ProbabilityTheory.cond_isProbabilityMeasure_of_finite x.2.1 x.2.2⟩ :=
      fun x => dif_pos x.2
    have hneg : ∀ x : ({p : Bel P × Act P |
        nextLaw P p.1.1 p.2 (Ioi 0) ≠ 0 ∧ nextLaw P p.1.1 p.2 (Ioi 0) ≠ ⊤}ᶜ : Set _),
        post P x.1.1.1 x.1.2 = ⟨Measure.dirac 0, inferInstance⟩ :=
      fun x => dif_neg x.2
    refine measurable_of_restrict_of_restrict_compl hset ?_ ?_
    · show Measurable (fun x : {p : Bel P × Act P |
        nextLaw P p.1.1 p.2 (Ioi 0) ≠ 0 ∧ nextLaw P p.1.1 p.2 (Ioi 0) ≠ ⊤} => post P x.1.1.1 x.1.2)
      rw [funext hpos]
      exact (hc.comp measurable_subtype_coe).subtype_mk
    · show Measurable (fun x : ({p : Bel P × Act P |
        nextLaw P p.1.1 p.2 (Ioi 0) ≠ 0 ∧ nextLaw P p.1.1 p.2 (Ioi 0) ≠ ⊤}ᶜ : Set _) =>
          post P x.1.1.1 x.1.2)
      rw [funext hneg]
      exact measurable_const
  have hsm : MeasurableSet
      {z : ProbabilityMeasure ℝ≥0 | secondMoment (z : Measure ℝ≥0) < ⊤} := by
    have h1 : Measurable (fun z : ProbabilityMeasure ℝ≥0 => secondMoment (z : Measure ℝ≥0)) := by
      unfold secondMoment
      exact (Measure.measurable_lintegral (by fun_prop)).comp measurable_subtype_coe
    exact h1 measurableSet_Iio
  have htoBel : Measurable (toBel P) := by
    have hpos : ∀ x : {z : ProbabilityMeasure ℝ≥0 | secondMoment (z : Measure ℝ≥0) < ⊤},
        toBel P x.1 = ⟨x.1, x.2⟩ := fun x => dif_pos x.2
    have hneg : ∀ x : ({z : ProbabilityMeasure ℝ≥0 | secondMoment (z : Measure ℝ≥0) < ⊤}ᶜ :
        Set _), toBel P x.1 = δ0 P := fun x => dif_neg x.2
    refine measurable_of_restrict_of_restrict_compl hsm ?_ ?_
    · show Measurable (fun x : {z : ProbabilityMeasure ℝ≥0 | secondMoment (z : Measure ℝ≥0) < ⊤}
        => toBel P x.1)
      rw [funext hpos]
      exact measurable_subtype_coe.subtype_mk
    · show Measurable (fun x : ({z : ProbabilityMeasure ℝ≥0 | secondMoment (z : Measure ℝ≥0) < ⊤}ᶜ
        : Set _) => toBel P x.1)
      rw [funext hneg]
      exact measurable_const
  have hqm : Measurable (fun p : Bel P × Act P => qBel P p.1 p.2) := by
    refine Measure.measurable_of_measurable_coe _ (fun E hE => ?_)
    simp only [qBel, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hE]
    refine (hR0.mul measurable_const).add (hR1.mul ?_)
    exact (measurable_const.indicator hE).comp (htoBel.comp hpost)
  let q : Kernel (Bel P × Act P) (Bel P) := ⟨fun p => qBel P p.1 p.2, hqm⟩
  have hmk : IsMarkovKernel q := by
    refine ⟨fun p => ⟨?_⟩⟩
    show qBel P p.1 p.2 univ = 1
    simp only [qBel, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    unfold R0 R1
    rw [← measure_union (by simp) measurableSet_Ioi]
    have : ({0} ∪ Ioi 0 : Set ℝ≥0) = univ := by
      ext x; simp only [mem_union, mem_singleton_iff, mem_Ioi, mem_univ, iff_true]
      exact (eq_or_ne x 0).imp id pos_iff_ne_zero.2
    rw [this]
    haveI : IsProbabilityMeasure (nextLaw P p.1.1 p.2) := by
      unfold nextLaw
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    exact measure_univ
  exact ⟨{ lower := 0, cost := fun z a => cbar P z a, q := q, isMarkov := hmk },
    rfl, fun _ _ => rfl, fun _ _ => rfl⟩

