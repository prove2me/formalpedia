-- Prove2me | solution 1 for ServiceParts.Shortfall.discrete_transition_probabilities
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:25:27.652185+00:00
-- url     : https://prove2.me/submissions/1a9d81ed-25b7-4ab6-9426-9e9cfc717fe3

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_DiscreteShortfallModel

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Shortfall.TP7f64

open MeasureTheory ProbabilityTheory

theorem shortfall_succ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : DiscreteShortfallModel Ω P) (k : ℕ) (ω : Ω) :
    M.shortfall (k + 1) ω =
      ((M.shortfall k ω : ℤ) + (M.demand (k + 1) ω : ℤ) - (M.capacity : ℤ)).toNat := rfl

theorem shortfall_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : DiscreteShortfallModel Ω P) (n : ℕ) :
    ∀ k ≤ n, Measurable[⨆ i ∈ Set.Iic n, MeasurableSpace.comap (M.demand i) inferInstance]
      (M.shortfall k) := by
  intro k
  induction k with
  | zero => intro _; exact measurable_const
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 : Measurable[⨆ i ∈ Set.Iic n, MeasurableSpace.comap (M.demand i) inferInstance]
        (M.demand (k + 1)) := by
      apply Measurable.of_comap_le
      exact le_iSup₂ (f := fun i (_ : i ∈ Set.Iic n) =>
        MeasurableSpace.comap (M.demand i) inferInstance) (k + 1) (by simp; omega)
    have h3 := (measurable_of_countable
      (fun p : ℕ × ℕ => ((p.1 : ℤ) + (p.2 : ℤ) - (M.capacity : ℤ)).toNat)).comp
      (h1.prodMk h2)
    exact h3

theorem main {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : DiscreteShortfallModel Ω P) (n : ℕ) (x : ℕ → ℕ) (j : ℕ) :
    (P {ω | (∀ k ≤ n, M.shortfall k ω = x k) ∧ M.shortfall (n + 1) ω = j}).toReal =
      (P {ω | ∀ k ≤ n, M.shortfall k ω = x k}).toReal * M.transProb (x n) j := by
  set A : Set Ω := {ω | ∀ k ≤ n, M.shortfall k ω = x k} with hAdef
  set S : Set ℕ := {d | ((x n : ℤ) + (d : ℤ) - (M.capacity : ℤ)).toNat = j} with hSdef
  have hAB : {ω | (∀ k ≤ n, M.shortfall k ω = x k) ∧ M.shortfall (n + 1) ω = j}
      = A ∩ M.demand (n + 1) ⁻¹' S := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, hAdef, hSdef,
      shortfall_succ]
    constructor
    · rintro ⟨h, h2⟩
      refine ⟨h, ?_⟩
      rw [← h n le_rfl]; exact h2
    · rintro ⟨h, h2⟩
      refine ⟨h, ?_⟩
      rw [h n le_rfl]; exact h2
  have hind := indep_iSup_of_disjoint
    (m := fun i => MeasurableSpace.comap (M.demand i) inferInstance)
    (fun i => (M.demand_measurable i).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).1 M.demand_indep)
    (S := Set.Iic n) (T := {n + 1}) (by simp)
  have hA : MeasurableSet[⨆ i ∈ Set.Iic n, MeasurableSpace.comap (M.demand i) inferInstance]
      A := by
    have : A = ⋂ k ∈ Finset.range (n + 1), M.shortfall k ⁻¹' {x k} := by
      ext ω; simp [hAdef]
    rw [this]
    refine Finset.measurableSet_biInter _ (fun k hk => ?_)
    exact shortfall_meas M n k (by simp at hk; omega) (measurableSet_singleton _)
  have hB : MeasurableSet[⨆ i ∈ ({n + 1} : Set ℕ),
      MeasurableSpace.comap (M.demand i) inferInstance] (M.demand (n + 1) ⁻¹' S) := by
    have : MeasurableSet[MeasurableSpace.comap (M.demand (n + 1)) inferInstance]
        (M.demand (n + 1) ⁻¹' S) := ⟨S, MeasurableSet.of_discrete, rfl⟩
    exact le_iSup₂ (f := fun i (_ : i ∈ ({n + 1} : Set ℕ)) =>
      MeasurableSpace.comap (M.demand i) inferInstance) (n + 1) rfl _ this
  have hmul := (Indep_iff _ _ _).1 hind A _ hA hB
  have hid : P (M.demand (n + 1) ⁻¹' S) = P (M.demand 1 ⁻¹' S) :=
    (M.demand_identDistrib (n + 1)).measure_mem_eq MeasurableSet.of_discrete
  rw [hAB, hmul, hid, ENNReal.toReal_mul]
  congr 1
  unfold DiscreteShortfallModel.transProb
  split_ifs with h0 hle hle'
  · congr 2; ext ω; simp only [Set.mem_preimage, hSdef, Set.mem_ofPred_eq]; omega
  · have : M.demand 1 ⁻¹' S = ∅ := by
      ext ω; simp only [Set.mem_preimage, hSdef, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false]; omega
    simp [this]
  · congr 2; ext ω; simp only [Set.mem_preimage, hSdef, Set.mem_ofPred_eq]; omega
  · have : M.demand 1 ⁻¹' S = ∅ := by
      ext ω; simp only [Set.mem_preimage, hSdef, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false]; omega
    simp [this]

end ServiceParts.Shortfall.TP7f64

open ServiceParts.Shortfall MeasureTheory ProbabilityTheory Filter Topology in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : DiscreteShortfallModel Ω P) (n : ℕ) (x : ℕ → ℕ) (j : ℕ) :
    (P {ω | (∀ k ≤ n, M.shortfall k ω = x k) ∧ M.shortfall (n + 1) ω = j}).toReal =
      (P {ω | ∀ k ≤ n, M.shortfall k ω = x k}).toReal * M.transProb (x n) j := by
  exact ServiceParts.Shortfall.TP7f64.main M n x j
