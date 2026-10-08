-- Prove2me | solution 2 for TalagrandConc.Assignment.lemma_10_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:36:47.181009+00:00
-- url     : https://prove2.me/submissions/b4bf430b-96e2-4a1c-b035-444e92222a92

import Mathlib



namespace TalagrandConc.Assignment

open MeasureTheory ProbabilityTheory

/-- The number of events that occur, as a sum of indicators. -/
lemma count_eq_sum {Ω : Type} {N : ℕ} (A : Fin N → Set Ω) (ω : Ω) :
    (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) =
      ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  simp only [Set.toFinset_ofPred, Finset.card_filter, Nat.cast_sum, Set.indicator_apply]
  push_cast
  rfl

/-- `exp (t · 1_A) = 1 + (e^t − 1) 1_A`. -/
lemma exp_mul_indicator {Ω : Type} (A : Set Ω) (t : ℝ) (ω : Ω) :
    Real.exp (t * A.indicator (fun _ => (1 : ℝ)) ω) =
      1 + (Real.exp t - 1) * A.indicator (fun _ => (1 : ℝ)) ω := by
  by_cases h : ω ∈ A
  · simp [h]
  · simp [h]

lemma mgf_indicator {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (t : ℝ) :
    mgf (A.indicator (fun _ => (1 : ℝ))) P t = 1 + (Real.exp t - 1) * P.real A := by
  unfold mgf
  simp_rw [exp_mul_indicator]
  rw [integral_add (integrable_const _) (((integrable_const _).indicator hA).const_mul _),
    integral_const, integral_const_mul]
  have : ∫ a, A.indicator (fun _ => (1 : ℝ)) a ∂P = P.real A := integral_indicator_one hA
  rw [this]
  simp

lemma integrable_exp_indicator {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * A.indicator (fun _ => (1 : ℝ)) ω)) P := by
  simp_rw [exp_mul_indicator]
  exact (integrable_const _).add (((integrable_const _).indicator hA).const_mul _)

/-- Elementary bound: for `0 ≤ s ≤ 1`, `exp (-s) ≤ 1 - s + s ^ 2`. -/
lemma exp_neg_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (-s) ≤ 1 - s + s ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := -s) (by rw [abs_neg, abs_of_nonneg hs0]; exact hs1)
  rw [abs_le] at h
  have := h.2
  nlinarith

theorem lemma_10_4_core :
    ∀ δ : ℝ, δ < 1 → ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : ℕ) (A : Fin N → Set Ω) (p : ℝ),
        (∀ i, MeasurableSet (A i)) → iIndepSet A P → (∀ i, P.real (A i) = p) →
        P {ω | (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) < δ * p * N} ≤
          ENNReal.ofReal (Real.exp (-((N : ℝ) * p) / K)) := by
  intro δ hδ
  have h1δ : 0 < 1 - δ := by linarith
  refine ⟨4 / (1 - δ) ^ 2, by positivity, ?_⟩
  intro Ω _ P _ N A p hA hind hp
  -- the sum of indicators
  set X : Fin N → Ω → ℝ := fun i => (A i).indicator (fun _ => (1 : ℝ)) with hX
  have hXm : ∀ i, Measurable (X i) := fun i => measurable_const.indicator (hA i)
  have hcount : ∀ ω, (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) = (∑ i, X i) ω := by
    intro ω
    rw [count_eq_sum, Finset.sum_apply]
  have hindf : iIndepFun X P := hind.iIndepFun_indicator
  -- p ≥ 0 when N ≥ 1
  by_cases h0 : δ * p * N ≤ 0
  · have : {ω | (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) < δ * p * N} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_trans h0 (Nat.cast_nonneg _)
    rw [this]; simp
  push_neg at h0
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at h0
    · exact h
  have hp0 : 0 ≤ p := by
    rw [← hp ⟨0, hN⟩]; exact measureReal_nonneg
  have hδ0 : 0 < δ := by
    by_contra hc
    push_neg at hc
    have : δ * p * N ≤ 0 := by
      have : 0 ≤ p * N := by positivity
      nlinarith
    linarith
  -- Chernoff with t = -s, s = (1 - δ)/2
  set s : ℝ := (1 - δ) / 2 with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      Integrable (fun ω => Real.exp ((-s) * X i ω)) P :=
    fun i _ => integrable_exp_indicator P (A i) (hA i) (-s)
  have hcher := measure_le_le_exp_mul_mgf (μ := P) (X := ∑ i, X i) (t := -s) (δ * p * N)
    (by linarith) (hindf.integrable_exp_mul_sum hXm hint)
  rw [hindf.mgf_sum hXm] at hcher
  have hmgf : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      mgf (X i) P (-s) = 1 + (Real.exp (-s) - 1) * p := by
    intro i _
    rw [hX]; dsimp only
    rw [mgf_indicator P (A i) (hA i), hp i]
  rw [Finset.prod_congr rfl hmgf, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcher
  -- bound the product
  have hbase0 : 0 ≤ 1 + (Real.exp (-s) - 1) * p := by
    rw [← hmgf ⟨0, hN⟩ (Finset.mem_univ _)]; exact mgf_nonneg
  have hbase : 1 + (Real.exp (-s) - 1) * p ≤ Real.exp (-(p * (1 - Real.exp (-s)))) := by
    have := Real.add_one_le_exp (-(p * (1 - Real.exp (-s))))
    linarith
  have hpow : (1 + (Real.exp (-s) - 1) * p) ^ N ≤ Real.exp (-((N : ℝ) * p * (1 - Real.exp (-s)))) := by
    calc (1 + (Real.exp (-s) - 1) * p) ^ N ≤ (Real.exp (-(p * (1 - Real.exp (-s))))) ^ N :=
          pow_le_pow_left₀ hbase0 hbase N
      _ = Real.exp (-((N : ℝ) * p * (1 - Real.exp (-s)))) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
  -- the exponent
  have hexp : Real.exp (-(-s) * (δ * p * N)) * Real.exp (-((N : ℝ) * p * (1 - Real.exp (-s)))) ≤
      Real.exp (-((N : ℝ) * p) / (4 / (1 - δ) ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have he := exp_neg_le s hs0.le hs1
    have hNp : 0 ≤ (N : ℝ) * p := by positivity
    have hkey : (1 - δ) ^ 2 / 4 ≤ (1 - Real.exp (-s)) - s * δ := by
      have : s * (1 - δ - s) = s ^ 2 := by rw [hs]; ring
      nlinarith
    have : -((N : ℝ) * p) / (4 / (1 - δ) ^ 2) = -((N : ℝ) * p) * ((1 - δ) ^ 2 / 4) := by
      field_simp
    rw [this]
    nlinarith
  have hreal : P.real {ω | (∑ i, X i) ω ≤ δ * p * N} ≤
      Real.exp (-((N : ℝ) * p) / (4 / (1 - δ) ^ 2)) := by
    refine le_trans hcher (le_trans ?_ hexp)
    exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
  calc P {ω | (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) < δ * p * N}
      ≤ P {ω | (∑ i, X i) ω ≤ δ * p * N} := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        rw [← hcount]; exact hω.le
    _ = ENNReal.ofReal (P.real {ω | (∑ i, X i) ω ≤ δ * p * N}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) * p) / (4 / (1 - δ) ^ 2))) :=
        ENNReal.ofReal_le_ofReal hreal

end TalagrandConc.Assignment

open TalagrandConc.Assignment
open MeasureTheory ProbabilityTheory

theorem solution :
    ∀ δ : ℝ, δ < 1 → ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : ℕ) (A : Fin N → Set Ω) (p : ℝ),
        (∀ i, MeasurableSet (A i)) → iIndepSet A P → (∀ i, P.real (A i) = p) →
        P {ω | (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) < δ * p * N} ≤
          ENNReal.ofReal (Real.exp (-((N : ℝ) * p) / K)) := by
  exact lemma_10_4_core
