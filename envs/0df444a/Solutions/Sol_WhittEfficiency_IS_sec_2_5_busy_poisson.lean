-- Prove2me | solution 1 for WhittEfficiency.IS.sec_2_5_busy_poisson
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:26:04.696585+00:00
-- url     : https://prove2.me/submissions/afcbbe86-3928-4ffd-a78b-233afc564af1

import Mathlib
import Definitions.Def_WhittEfficiency_IS_Model
import Theorems.Thm_WhittEfficiency_IS_sec_2_5_class_counts

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

namespace WhittBusyPoissonAux

/-- `ω ↦ #{j | ω ∈ C j}` is measurable when every `C j` is. -/
theorem measurable_ncard_setOf {Ω : Type*} [MeasurableSpace Ω] (C : ℕ → Set Ω)
    (hC : ∀ j, MeasurableSet (C j)) :
    Measurable (fun ω => {j : ℕ | ω ∈ C j}.ncard) := by
  apply measurable_to_countable'
  intro k
  have hfin : MeasurableSet {ω | {j : ℕ | ω ∈ C j}.Finite} := by
    have : {ω | {j : ℕ | ω ∈ C j}.Finite} = ⋃ N : ℕ, ⋂ j : ℕ, ⋂ (_ : N ≤ j), (C j)ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_compl_iff]
      constructor
      · intro h
        obtain ⟨N, hN⟩ := h.bddAbove
        refine ⟨N + 1, fun j hj hjC => ?_⟩
        have := hN hjC
        omega
      · rintro ⟨N, hN⟩
        apply (Set.finite_lt_nat N).subset
        intro j hj
        by_contra hjN
        exact hN j (by simp at hjN; omega) hj
    rw [this]
    exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hC j).compl
  have hEq : ∀ F : Finset ℕ, MeasurableSet {ω | {j : ℕ | ω ∈ C j} = (F : Set ℕ)} := by
    intro F
    have : {ω | {j : ℕ | ω ∈ C j} = (F : Set ℕ)} =
        ⋂ j : ℕ, {ω | ω ∈ C j ↔ j ∈ F} := by
      ext ω
      simp [Set.ext_iff]
    rw [this]
    refine MeasurableSet.iInter fun j => ?_
    by_cases hj : j ∈ F
    · have e : {ω | ω ∈ C j ↔ j ∈ F} = C j := by ext; simp [hj]
      rw [e]; exact hC j
    · have e : {ω | ω ∈ C j ↔ j ∈ F} = (C j)ᶜ := by ext; simp [hj]
      rw [e]; exact (hC j).compl
  have hset : (fun ω => {j : ℕ | ω ∈ C j}.ncard) ⁻¹' {k} =
      (⋃ F : Finset ℕ, ⋃ (_ : F.card = k), {ω | {j : ℕ | ω ∈ C j} = (F : Set ℕ)}) ∪
        ({ω | {j : ℕ | ω ∈ C j}.Finite}ᶜ ∩ {_ω | k = 0}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_iUnion,
      Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · intro h
      by_cases hf : {j : ℕ | ω ∈ C j}.Finite
      · left
        refine ⟨hf.toFinset, ?_, by simp⟩
        rw [← h, Set.ncard_eq_toFinset_card _ hf]
      · right
        exact ⟨hf, by rw [← h, Set.Infinite.ncard hf]⟩
    · rintro (⟨F, hF, hS⟩ | ⟨hf, hk⟩)
      · rw [hS, Set.ncard_coe_finset, hF]
      · rw [hk, Set.Infinite.ncard hf]
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.iUnion fun F => MeasurableSet.iUnion fun _ => hEq F) ?_
  refine hfin.compl.inter ?_
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk]

end WhittBusyPoissonAux

open WhittBusyPoissonAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    {m : ℕ} (p d : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i) (J : ℕ → Ω → Fin m)
    (hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T p J)
    (hmean : ∑ i, p i * d i = 1) (t : ℝ) (ht : ∀ i, d i < t) :
    ∀ k : ℕ, μ.real {ω | WhittEfficiency.IS.busyCount T (fun j ω => d (J j ω)) t ω = k} =
      Real.exp (-lam) * lam ^ k / k.factorial := by
  obtain ⟨hind, hlaw, hae⟩ :=
    WhittEfficiency.IS.sec_2_5_class_counts μ lam hlam T p d hd J hM t ht
  set X : Fin m → Ω → ℕ := fun i ω => WhittEfficiency.IS.classBusyCount T J d i t ω with hXdef
  -- nonnegativity of the label probabilities
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    rw [← hM.label_law 0 i]
    exact measureReal_nonneg
  have hr : ∀ i, 0 ≤ lam * p i * d i := fun i =>
    mul_nonneg (mul_nonneg hlam.le (hp i)) (hd i)
  let r : Fin m → NNReal := fun i => ⟨lam * p i * d i, hr i⟩
  -- measurability of the class counts
  have hTm : ∀ n, Measurable (arrivalTime T n) := by
    intro n
    unfold arrivalTime
    exact Finset.measurable_sum _ fun i _ => hM.arrivals.measurable i
  have hXm : ∀ i, Measurable (X i) := by
    intro i
    have := measurable_ncard_setOf
      (fun j => {ω | J j ω = i ∧ arrivalTime T (j + 1) ω ≤ t ∧
        t < arrivalTime T (j + 1) ω + d i}) (fun j => by
        refine MeasurableSet.inter ((hM.label_measurable j) (measurableSet_singleton i)) ?_
        refine MeasurableSet.inter (measurableSet_le (hTm _) measurable_const) ?_
        exact measurableSet_lt measurable_const ((hTm _).add measurable_const))
    exact this
  -- each class count is Poisson
  have hXlaw : ∀ i, HasLaw (X i) (poissonMeasure (r i)) μ := by
    intro i
    refine ⟨(hXm i).aemeasurable, ?_⟩
    apply Measure.ext_of_singleton
    intro a
    rw [Measure.map_apply (hXm i) (measurableSet_singleton a), poissonMeasure_singleton,
      ← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    congr 1
    change μ.real {ω | X i ω = a} = _
    rw [hlaw i a]
    rfl
  -- the sum over any finset is Poisson
  have hsum : ∀ s : Finset (Fin m),
      HasLaw (∑ i ∈ s, X i) (poissonMeasure (∑ i ∈ s, r i)) μ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      refine ⟨aemeasurable_const, ?_⟩
      apply Measure.ext_of_singleton
      intro a
      show Measure.map (fun _ => (0:ℕ)) μ {a} = _
      rw [Measure.map_apply (measurable_const (a := (0:ℕ))) (measurableSet_singleton a),
        poissonMeasure_singleton]
      by_cases h0 : a = 0
      · subst h0
        simp
      · have : (fun _ : Ω => (0 : ℕ)) ⁻¹' {a} = ∅ := by
          ext ω; simp [Ne.symm h0]
        rw [this]
        simp [h0]
    | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      have hI : IndepFun (X a) (∑ i ∈ s, X i) μ :=
        (hind.indepFun_finsetSum_of_notMem (fun i => hXm i) has).symm
      exact hI.hasLaw_add_poissonMeasure (hXlaw a) ih
  have hfull := hsum Finset.univ
  have hR : ((∑ i, r i : NNReal) : ℝ) = lam := by
    rw [NNReal.coe_sum]
    change ∑ i, lam * p i * d i = lam
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hmean, mul_one]
  intro k
  have hcongr : μ.real {ω | WhittEfficiency.IS.busyCount T (fun j ω => d (J j ω)) t ω = k} =
      μ.real ((∑ i, X i) ⁻¹' {k}) := by
    apply measureReal_congr
    filter_upwards [hae] with ω hω
    change (WhittEfficiency.IS.busyCount T (fun j ω => d (J j ω)) t ω = k) =
      ((∑ i, X i) ω = k)
    rw [hω, Finset.sum_apply]
  have hSm : Measurable (∑ i, X i) := by
    have e : (∑ i, X i) = fun ω => ∑ i, X i ω := by ext; simp
    rw [e]; exact Finset.measurable_sum _ fun i _ => hXm i
  rw [hcongr, ← map_measureReal_apply hSm
    (measurableSet_singleton k), hfull.map_eq, poissonMeasure_real_singleton, hR]
