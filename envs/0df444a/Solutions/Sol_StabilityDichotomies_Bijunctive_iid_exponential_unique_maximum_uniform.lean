-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.iid_exponential_unique_maximum_uniform
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:45:46.620347+00:00
-- url     : https://prove2.me/submissions/b0ba3591-acce-4cb5-b4a6-802ab78ecefb

import Theorems.Thm_StabilityDichotomies_Bijunctive_shifted_exponential_pair_tie_null
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

private def winner {n : ℕ} (i : Fin n) : Set (Fin n → ℝ) :=
  {δ | ∀ j, j ≠ i → δ j < δ i}

private theorem winner_measurable {n : ℕ} (i : Fin n) : MeasurableSet (winner i) := by
  unfold winner
  simp only [setOf_forall]
  apply MeasurableSet.iInter; intro j
  apply MeasurableSet.iInter; intro h
  exact measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)

theorem solution (n : ℕ) (β : ℝ) (hβ : 0 < β) (i : Fin n) :
    (Measure.pi (fun _ : Fin n => expMeasure β)
      {δ : Fin n → ℝ | ∀ j, j ≠ i → δ j < δ i}).toReal = 1 / n := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let μ : Measure (Fin n → ℝ) := Measure.pi (fun _ => expMeasure β)
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  have hpair : ∀ a b : Fin n, a ≠ b → μ {δ | δ a = δ b} = 0 := by
    intro a b hab
    have h := shifted_exponential_pair_tie_null n β hβ (fun _ => 0) a b hab
    simpa [μ] using h
  have hae : ∀ᵐ δ ∂μ, ∀ a b : Fin n, a ≠ b → δ a ≠ δ b := by
    apply ae_all_iff.mpr; intro a
    apply ae_all_iff.mpr; intro b
    by_cases hab : a = b
    · simp [hab]
    · have hh : ∀ᵐ δ ∂μ, δ a ≠ δ b := by
        rw [ae_iff]
        have he : {δ : Fin n → ℝ | ¬(δ a ≠ δ b)} = {δ | δ a = δ b} := by ext δ; simp
        rw [he]
        exact hpair a b hab
      filter_upwards [hh] with δ hδ _
      exact hδ
  have hfull : (⋃ j : Fin n, winner j) =ᵐ[μ] Set.univ := by
    filter_upwards [hae] with δ hδ
    apply propext
    change δ ∈ (⋃ j : Fin n, winner j) ↔ δ ∈ Set.univ
    simp only [Set.mem_univ, iff_true, Set.mem_iUnion]
    obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image Finset.univ δ ⟨i,Finset.mem_univ i⟩
    refine ⟨j,?_⟩
    intro k hkj
    exact lt_of_le_of_ne (hmax k (Finset.mem_univ k)) (hδ k j hkj)
  have hdis : Pairwise (Disjoint on (winner (n := n))) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro δ ha hb
    exact (lt_asymm (ha b (Ne.symm hab))) (hb a hab)
  have hsum : (∑ j : Fin n, μ.real (winner j)) = 1 := by
    have h := measureReal_iUnion_fintype (μ := μ) hdis winner_measurable
    have hall : μ.real (⋃ j : Fin n, winner j) = 1 := by
      unfold Measure.real
      rw [measure_congr hfull, measure_univ, ENNReal.toReal_one]
    linarith
  have hequal (a b : Fin n) : μ.real (winner a) = μ.real (winner b) := by
    let e : Fin n ≃ Fin n := Equiv.swap a b
    have hmp := measurePreserving_piCongrLeft (fun _ : Fin n => expMeasure β) e
    have hp := hmp.measure_preimage (winner_measurable b).nullMeasurableSet
    have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e) ⁻¹' winner b = winner a := by
      ext δ
      simp only [mem_preimage,winner,mem_setOf_eq,MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply,eq_rec_constant]
      constructor
      · intro h k hka
        have hh := h (e k) (by
          intro heq
          have h' := congrArg e.symm heq
          apply hka
          simpa [e] using h')
        simpa [e] using hh
      · intro h k hkb
        have hk : e.symm k ≠ a := by
          intro heq
          have h' := congrArg e heq
          apply hkb
          simpa [e] using h'
        have hh := h (e.symm k) hk
        simpa [e] using hh
    rw [he] at hp
    exact congrArg ENNReal.toReal hp
  have heqsum : (∑ j : Fin n, μ.real (winner j)) = n * μ.real (winner i) := by
    calc
      _ = ∑ _j : Fin n, μ.real (winner i) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hequal j i
      _ = n * μ.real (winner i) := by simp
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  rw [heqsum] at hsum
  change μ.real (winner i) = 1 / n
  field_simp
  linarith
