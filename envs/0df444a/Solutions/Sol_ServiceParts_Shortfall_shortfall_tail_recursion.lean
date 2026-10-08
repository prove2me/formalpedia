-- Prove2me | solution 1 for ServiceParts.Shortfall.shortfall_tail_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:57:59.763402+00:00
-- url     : https://prove2.me/submissions/1b14cc3c-5b43-42db-a296-6e60620de4ba

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_ShortfallModel

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ServiceParts.Shortfall.P2MAux74997d72

theorem shortfall_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) : ∀ (n : ℕ) (ω : Ω), 0 ≤ M.shortfall n ω
  | 0, _ => le_rfl
  | _ + 1, _ => le_max_right _ _

theorem shortfall_meas_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) (n : ℕ) :
    ∀ k, k ≤ n →
      Measurable[⨆ i ∈ Set.Iic n, MeasurableSpace.comap (M.demand i) inferInstance]
        (M.shortfall k) := by
  intro k
  induction k with
  | zero => intro _; exact measurable_const
  | succ k ih =>
    intro hk
    have hd : Measurable[⨆ i ∈ Set.Iic n, MeasurableSpace.comap (M.demand i) inferInstance]
        (M.demand (k + 1)) := by
      apply Measurable.of_comap_le
      exact le_iSup₂ (f := fun i (_ : i ∈ Set.Iic n) =>
        MeasurableSpace.comap (M.demand i) inferInstance) (k + 1) (by simp; omega)
    have ih' := ih (by omega)
    show Measurable[⨆ i ∈ Set.Iic n, MeasurableSpace.comap (M.demand i) inferInstance]
      (fun ω => max (M.shortfall k ω + M.demand (k + 1) ω - M.capacity) 0)
    exact Measurable.max ((ih'.add hd).sub_const _) measurable_const

theorem shortfall_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) (n : ℕ) :
    Measurable (M.shortfall n) :=
  (shortfall_meas_le M n n le_rfl).mono
    (iSup₂_le fun i _ => (M.demand_measurable i).comap_le) le_rfl

theorem indep_shortfall_demand {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) (n : ℕ) :
    IndepFun (M.shortfall n) (M.demand (n + 1)) P := by
  rw [IndepFun_iff_Indep]
  have h := indep_iSup_of_disjoint
    (m := fun i => MeasurableSpace.comap (M.demand i) inferInstance)
    (fun i => (M.demand_measurable i).comap_le) M.demand_indep.iIndep
    (S := Set.Iic n) (T := {n + 1}) (by simp)
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h
    (shortfall_meas_le M n n le_rfl).comap_le) ?_
  exact le_iSup₂ (f := fun i (_ : i ∈ ({n + 1} : Set ℕ)) =>
    MeasurableSpace.comap (M.demand i) inferInstance) (n + 1) (Set.mem_singleton _)

end ServiceParts.Shortfall.P2MAux74997d72

open MeasureTheory ProbabilityTheory ServiceParts.Shortfall in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) (n : ℕ) (v : ℝ) (hv : 0 < v) :
    P {ω | v < M.shortfall (n + 1) ω} =
        P {ω | v < M.shortfall n ω + M.demand (n + 1) ω - M.capacity} ∧
    P {ω | v < M.shortfall n ω + M.demand (n + 1) ω - M.capacity} =
        P {ω | v + M.capacity < M.demand (n + 1) ω} +
          ∫⁻ d, (Set.Iic (v + M.capacity)).indicator
              (fun x => P {ω | v + M.capacity - x < M.shortfall n ω}) d
            ∂(P.map (M.demand (n + 1))) := by
  have hVm := ServiceParts.Shortfall.P2MAux74997d72.shortfall_measurable M n
  have hDm := M.demand_measurable (n + 1)
  have hind := ServiceParts.Shortfall.P2MAux74997d72.indep_shortfall_demand M n
  refine ⟨?_, ?_⟩
  · congr 1
    ext ω
    simp only [Set.mem_setOf_eq]
    show v < max (M.shortfall n ω + M.demand (n + 1) ω - M.capacity) 0 ↔ _
    rw [lt_max_iff]
    constructor
    · rintro (h | h)
      · exact h
      · linarith
    · exact Or.inl
  · set c := M.capacity with hc
    have hS : MeasurableSet {p : ℝ × ℝ | v < p.1 + p.2 - c} :=
      measurableSet_lt measurable_const ((measurable_fst.add measurable_snd).sub_const c)
    have h1 : P {ω | v < M.shortfall n ω + M.demand (n + 1) ω - c} =
        (P.map (M.shortfall n)).prod (P.map (M.demand (n + 1))) {p | v < p.1 + p.2 - c} := by
      rw [← (indepFun_iff_map_prod_eq_prod_map_map hVm.aemeasurable hDm.aemeasurable).1 hind,
        Measure.map_apply (hVm.prodMk hDm) hS]
      rfl
    rw [h1, Measure.prod_apply_symm hS]
    have h2 : ∀ d : ℝ, (P.map (M.shortfall n)) ((fun x => (x, d)) ⁻¹' {p : ℝ × ℝ | v < p.1 + p.2 - c})
        = (Set.Ioi (v + c)).indicator 1 d +
          (Set.Iic (v + c)).indicator (fun x => P {ω | v + c - x < M.shortfall n ω}) d := by
      intro d
      have hs : MeasurableSet ((fun x => (x, d)) ⁻¹' {p : ℝ × ℝ | v < p.1 + p.2 - c}) :=
        measurable_prodMk_right hS
      rw [Measure.map_apply hVm hs]
      by_cases hd : d ≤ v + c
      · rw [Set.indicator_of_notMem (by simpa using hd), Set.indicator_of_mem (by simpa using hd),
          zero_add]
        congr 1
        ext ω
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        constructor <;> intro h <;> linarith
      · rw [Set.indicator_of_mem (by simpa using hd), Set.indicator_of_notMem (by simpa using hd),
          add_zero, Pi.one_apply]
        have hset : (M.shortfall n) ⁻¹' ((fun x => (x, d)) ⁻¹' {p : ℝ × ℝ | v < p.1 + p.2 - c})
            = Set.univ := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
          have := ServiceParts.Shortfall.P2MAux74997d72.shortfall_nonneg M n ω
          have hd' := lt_of_not_ge hd
          linarith
        rw [hset, measure_univ]
    simp_rw [h2]
    rw [lintegral_add_left (measurable_one.indicator measurableSet_Ioi),
      lintegral_indicator_one measurableSet_Ioi, Measure.map_apply hDm measurableSet_Ioi]
    rfl
