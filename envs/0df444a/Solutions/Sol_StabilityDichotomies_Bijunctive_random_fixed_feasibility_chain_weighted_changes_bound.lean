-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.random_fixed_feasibility_chain_weighted_changes_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:14:42.371935+00:00
-- url     : https://prove2.me/submissions/cb019022-46c3-41e3-ab6c-ff02ee3e37ae

import Theorems.Thm_StabilityDichotomies_Bijunctive_fixed_feasibility_chain_total_changes_harmonic_bound
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution
    {Γ : Language} {V J : Type} [Fintype V] [Fintype J]
    (rep : TwoCNFRepresentation Γ) (I G : Instance Γ V) (hI : Satisfiable I)
    (F : J → ℕ → Instance Γ V) (k : J → ℕ)
    (hG : ∀ j c, c ∈ G.constraints → c ∈ (F j 0).constraints)
    (hbase : ∀ j i, i ≤ k j → ∀ c ∈ (F j 0).constraints, c ∈ (F j i).constraints)
    (hIcontains : ∀ j i, i ≤ k j → ∀ c ∈ (F j i).constraints, c ∈ I.constraints)
    (hchain : ∀ j i, i < k j → ∀ c ∈ (F j i).constraints, c ∈ (F j (i+1)).constraints)
    (β : ℝ) (hβ : 0 < β) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hp_sum : ∑ j, p j = 1) (a : J → ℕ → ℝ)
    (_ha0 : ∀ j i, 0 ≤ a j i) (ha1 : ∀ j i, a j i ≤ 1) :
    (∑ j, p j * ∑ i ∈ Finset.range (k j), a j i * ∑ v : V,
      (Measure.pi (fun _ : Literal V => expMeasure β)
        {δ : Literal V → ℝ |
          decide (literalScore rep G (F j i) δ (v,false) < literalScore rep G (F j i) δ (v,true)) ≠
          decide (literalScore rep G (F j (i+1)) δ (v,false) < literalScore rep G (F j (i+1)) δ (v,true))}).toReal) ≤
      (maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ) := by
  classical
  let Q : J → ℕ → ℝ := fun j i => ∑ v : V,
      (Measure.pi (fun _ : Literal V => expMeasure β)
        {δ : Literal V → ℝ |
          decide (literalScore rep G (F j i) δ (v,false) < literalScore rep G (F j i) δ (v,true)) ≠
          decide (literalScore rep G (F j (i+1)) δ (v,false) < literalScore rep G (F j (i+1)) δ (v,true))}).toReal
  let B : ℝ := (maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ)
  have hQ (j : J) (i : ℕ) : 0 ≤ Q j i := by
    apply Finset.sum_nonneg
    intro v hv
    exact ENNReal.toReal_nonneg
  have hj (j : J) : (∑ i ∈ Finset.range (k j), a j i * Q j i) ≤ B := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k j), Q j i := by
        apply Finset.sum_le_sum
        intro i hi
        simpa using mul_le_of_le_one_left (hQ j i) (ha1 j i)
      _ ≤ B := fixed_feasibility_chain_total_changes_harmonic_bound rep I G hI (F j) (k j)
        (hG j) (hbase j) (hIcontains j) (hchain j) β hβ
  change (∑ j, p j * ∑ i ∈ Finset.range (k j), a j i * Q j i) ≤ B
  calc
    _ ≤ ∑ j, p j * B := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hj j) (hp j))
    _ = B := by rw [← Finset.sum_mul, hp_sum, one_mul]
