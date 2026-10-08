-- Prove2me | solution 1 for PoissonDepTrials.MixInv.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:45:16.391744+00:00
-- url     : https://prove2.me/submissions/b7204431-9a30-4c75-8717-3f22defac961

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

open scoped symmDiff in
theorem c9ed5cdf_sub_le_symmDiff {S : Type*} [MeasurableSpace S] (ν : Measure S)
    [IsFiniteMeasure ν] (A B : Set S) : ν.real B - ν.real A ≤ ν.real (A ∆ B) := by
  have h1 : ν.real B ≤ ν.real A + ν.real (B \ A) := by
    calc ν.real B ≤ ν.real (A ∪ B \ A) :=
          measureReal_mono (by intro x hx; by_cases h : x ∈ A <;> simp [*])
      _ ≤ ν.real A + ν.real (B \ A) := measureReal_union_le _ _
  have h2 : ν.real (B \ A) ≤ ν.real (A ∆ B) :=
    measureReal_mono (by rw [Set.symmDiff_def]; exact Set.subset_union_right)
  linarith

open scoped symmDiff in
/-- If two finite measures differ by at most `α` on every set of a generating algebra,
they differ by at most `α` on every measurable set. -/
theorem c9ed5cdf_extend {S : Type*} [mS : MeasurableSpace S] (ν μ : Measure S)
    [IsFiniteMeasure ν] [IsFiniteMeasure μ] (C : Set (Set S)) (hC : IsSetAlgebra C)
    (hgen : mS = MeasurableSpace.generateFrom C) (α : ℝ)
    (hA : ∀ A ∈ C, |ν.real A - μ.real A| ≤ α) :
    ∀ B : Set S, MeasurableSet B → |ν.real B - μ.real B| ≤ α := by
  intro B hB
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have h'C : ∃ D : Set (Set S), D.Countable ∧ D ⊆ C ∧ (ν + μ) (⋃₀ D)ᶜ = 0 :=
    ⟨{Set.univ}, Set.countable_singleton _, by simpa using hC.univ_mem, by simp⟩
  obtain ⟨A, hAC, hAB⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := ν + μ) hC.isSetRing h'C hgen hB (ε := ENNReal.ofReal ε) (by simpa using hε)
  have hlt : (ν + μ).real (A ∆ B) < ε := ENNReal.toReal_lt_of_lt_ofReal hAB
  have hsum : (ν + μ).real (A ∆ B) = ν.real (A ∆ B) + μ.real (A ∆ B) := by
    simp [measureReal_def, ENNReal.toReal_add, measure_ne_top]
  have e1 := c9ed5cdf_sub_le_symmDiff ν A B
  have e2 := c9ed5cdf_sub_le_symmDiff ν B A
  have e3 := c9ed5cdf_sub_le_symmDiff μ A B
  have e4 := c9ed5cdf_sub_le_symmDiff μ B A
  rw [symmDiff_comm] at e2 e4
  have hA' := abs_le.mp (hA A hAC)
  rw [abs_lt]
  constructor <;> linarith [hA'.1, hA'.2]

open MeasureTheory ProbabilityTheory PoissonDepTrials.MixInv in
theorem solution {Ω R S : Type*} [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSpace S]
    [StandardBorelSpace S] [Nonempty S] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → R) (Z : Ω → S) (hY : Measurable Y) (hZ : Measurable Z) (α : ℝ)
    (h42 : ∀ B : Set S, MeasurableSet B →
      ∀ᵐ ω ∂P, |(P[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap Y inferInstance]) ω - P.real (Z ⁻¹' B)| ≤ α) :
    ∃ κ : Kernel R S, IsMarkovKernel κ ∧ (P.map Y) ⊗ₘ κ = P.map (fun ω => (Y ω, Z ω)) ∧
      ∃ M : Set R, MeasurableSet M ∧ P (Y ⁻¹' M) = 1 ∧
        ∀ y ∈ M, ∀ B : Set S, MeasurableSet B → |(κ y B).toReal - (P.map Z).real B| ≤ α := by
  set κ := condDistrib Z Y P with hκ
  -- step 1: a.e. bound for each fixed measurable set
  have hmeasB : ∀ B : Set S, MeasurableSet B →
      MeasurableSet {y : R | |(κ y).real B - (P.map Z).real B| ≤ α} := by
    intro B hB
    refine measurableSet_le ?_ measurable_const
    exact (((κ.measurable_coe hB).ennreal_toReal).sub_const _).abs
  have hstep1 : ∀ B : Set S, MeasurableSet B →
      ∀ᵐ y ∂(P.map Y), |(κ y).real B - (P.map Z).real B| ≤ α := by
    intro B hB
    rw [ae_map_iff hY.aemeasurable (hmeasB B hB)]
    filter_upwards [condDistrib_ae_eq_condExp hY hZ hB (μ := P), h42 B hB] with ω h1 h2
    rw [map_measureReal_apply hZ hB]
    rw [show (κ (Y ω)).real B = _ from h1]
    exact h2
  -- step 2: countable generating algebra
  set C := generateSetAlgebra (MeasurableSpace.countableGeneratingSet S) with hCdef
  have hCalg : IsSetAlgebra C := isSetAlgebra_generateSetAlgebra
  have hCcount : C.Countable :=
    countable_generateSetAlgebra MeasurableSpace.countable_countableGeneratingSet
  have hgen : (inferInstance : MeasurableSpace S) = MeasurableSpace.generateFrom C := by
    rw [hCdef, generateFrom_generateSetAlgebra_eq,
      MeasurableSpace.generateFrom_countableGeneratingSet]
  have hCmeas : ∀ A ∈ C, MeasurableSet A := by
    intro A hA
    have h := MeasurableSpace.measurableSet_generateFrom hA
    rw [← hgen] at h
    exact h
  set M : Set R := ⋂ A ∈ C, {y : R | |(κ y).real A - (P.map Z).real A| ≤ α} with hMdef
  have hM : MeasurableSet M := MeasurableSet.biInter hCcount fun A hA => hmeasB A (hCmeas A hA)
  have hMae : ∀ᵐ y ∂(P.map Y), y ∈ M := by
    have := (ae_ball_iff hCcount).2 fun A hA => hstep1 A (hCmeas A hA)
    filter_upwards [this] with y hy
    simp only [hMdef, Set.mem_iInter, Set.mem_ofPred_eq]
    exact hy
  have : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  refine ⟨κ, inferInstance, compProd_map_condDistrib hZ.aemeasurable, M, hM, ?_, ?_⟩
  · rw [← Measure.map_apply hY hM]
    have h0 : (P.map Y) Mᶜ = 0 := by
      rw [ae_iff] at hMae
      simpa [Set.compl_def] using hMae
    exact (prob_compl_eq_zero_iff hM).1 h0
  · intro y hy B hB
    have hyA : ∀ A ∈ C, |(κ y).real A - (P.map Z).real A| ≤ α := by
      intro A hA
      simp only [hMdef, Set.mem_iInter, Set.mem_ofPred_eq] at hy
      exact hy A hA
    have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
    exact c9ed5cdf_extend (κ y) (P.map Z) C hCalg hgen α hyA B hB
