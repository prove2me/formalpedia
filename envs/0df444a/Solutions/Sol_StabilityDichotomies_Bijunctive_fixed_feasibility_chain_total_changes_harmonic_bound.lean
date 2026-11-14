-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.fixed_feasibility_chain_total_changes_harmonic_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:10:40.50359+00:00
-- url     : https://prove2.me/submissions/4e2b1b37-a231-4d56-a189-7d2529be3d61

import Theorems.Thm_StabilityDichotomies_Bijunctive_fixed_feasibility_chain_bit_changes_harmonic_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_isolated_subinstance_literal_score_eq_own_shift
import Theorems.Thm_StabilityDichotomies_Solvability_nonisolated_variables_bound
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I G : Instance Γ V) (hI : Satisfiable I)
    (F : ℕ → Instance Γ V) (k : ℕ)
    (hG : ∀ c ∈ G.constraints, c ∈ (F 0).constraints)
    (hbase : ∀ i ≤ k, ∀ c ∈ (F 0).constraints, c ∈ (F i).constraints)
    (hIcontains : ∀ i ≤ k, ∀ c ∈ (F i).constraints, c ∈ I.constraints)
    (hchain : ∀ i < k, ∀ c ∈ (F i).constraints, c ∈ (F (i+1)).constraints)
    (β : ℝ) (hβ : 0 < β) :
    (∑ i ∈ Finset.range k, ∑ v : V,
      (Measure.pi (fun _ : Literal V => expMeasure β)
        {δ : Literal V → ℝ |
          decide (literalScore rep G (F i) δ (v,false) < literalScore rep G (F i) δ (v,true)) ≠
          decide (literalScore rep G (F (i+1)) δ (v,false) < literalScore rep G (F (i+1)) δ (v,true))}).toReal) ≤
      (maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ) := by
  classical
  let μ : Measure (Literal V → ℝ) := Measure.pi (fun _ => expMeasure β)
  let P : ℕ → V → ℝ := fun i v => μ.real {δ |
    decide (literalScore rep G (F i) δ (v,false) < literalScore rep G (F i) δ (v,true)) ≠
    decide (literalScore rep G (F (i+1)) δ (v,false) < literalScore rep G (F (i+1)) δ (v,true))}
  let U := I.constraints.toFinset.biUnion (fun c => Finset.univ.image c.scope)
  let B : ℝ := harmonic (Fintype.card (Literal V))
  have hGsub : ∀ c ∈ G.constraints, c ∈ I.constraints := fun c hc => hIcontains 0 (by omega) c (hG c hc)
  have hzero (v : V) (hv : v ∉ U) (i : ℕ) (hi : i < k) : P i v = 0 := by
    have hiso : ∀ c ∈ I.constraints, ∀ l : Fin c.rel.val.arity, c.scope l ≠ v := by
      intro c hc l hl
      apply hv
      apply Finset.mem_biUnion.mpr
      exact ⟨c,Multiset.mem_toFinset.mpr hc,Finset.mem_image.mpr ⟨l,Finset.mem_univ _,hl⟩⟩
    have he : {δ : Literal V → ℝ |
      decide (literalScore rep G (F i) δ (v,false) < literalScore rep G (F i) δ (v,true)) ≠
      decide (literalScore rep G (F (i+1)) δ (v,false) < literalScore rep G (F (i+1)) δ (v,true))} = ∅ := by
      apply Set.Subset.antisymm ?_ (Set.empty_subset _)
      intro δ hδ
      have hf := isolated_subinstance_literal_score_eq_own_shift rep I hI v hiso G (F i)
        hGsub (hIcontains i (by omega)) δ false
      have ht := isolated_subinstance_literal_score_eq_own_shift rep I hI v hiso G (F i)
        hGsub (hIcontains i (by omega)) δ true
      have hf' := isolated_subinstance_literal_score_eq_own_shift rep I hI v hiso G (F (i+1))
        hGsub (hIcontains (i+1) (by omega)) δ false
      have ht' := isolated_subinstance_literal_score_eq_own_shift rep I hI v hiso G (F (i+1))
        hGsub (hIcontains (i+1) (by omega)) δ true
      change decide (literalScore rep G (F i) δ (v,false) < literalScore rep G (F i) δ (v,true)) ≠
        decide (literalScore rep G (F (i+1)) δ (v,false) < literalScore rep G (F (i+1)) δ (v,true)) at hδ
      apply False.elim
      apply hδ
      rw [hf,ht,hf',ht']
    change μ.real _ = 0
    rw [he,measureReal_empty]
  have hV (v : V) : (∑ i ∈ Finset.range k, P i v) ≤ B :=
    fixed_feasibility_chain_bit_changes_harmonic_bound rep I G hI F k v hG hbase hIcontains hchain β hβ
  have hB : 0 ≤ B := by
    dsimp [B]
    simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    positivity
  change (∑ i ∈ Finset.range k, ∑ v : V, P i v) ≤ _
  rw [Finset.sum_comm]
  have hU : (∑ v : V, ∑ i ∈ Finset.range k, P i v) = ∑ v ∈ U, ∑ i ∈ Finset.range k, P i v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ U)
    intro v _ hv
    apply Finset.sum_eq_zero
    intro i hi
    exact hzero v hv i (Finset.mem_range.mp hi)
  rw [hU]
  calc
    (∑ v ∈ U, ∑ i ∈ Finset.range k, P i v) ≤ (U.card : ℝ) * B := by
      simpa using Finset.sum_le_card_nsmul U (fun v => ∑ i ∈ Finset.range k, P i v) B (fun v _ => hV v)
    _ ≤ (maxArity Γ * I.constraints.card : ℕ) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast nonisolated_variables_bound I
