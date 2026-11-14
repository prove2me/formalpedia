-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.expected_total_seed_graph_deletion_changes_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:31:54.001207+00:00
-- url     : https://prove2.me/submissions/d6a920e6-dd31-4ad7-a658-a8682118c64d

import Theorems.Thm_StabilityDichotomies_Bijunctive_expected_seed_graph_deletion_changes_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_isolated_variable_graph_deletion_score_unchanged
import Theorems.Thm_StabilityDichotomies_Solvability_nonisolated_variables_bound
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V] [Nonempty V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (ε : ℝ) (hε : 0 < ε) :
    let μ := bijunctiveSeedMeasure rep I ε
    let C := fun (v : V) (s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) =>
      ∑ j : Fin I.constraints.card,
        if decide (literalScore rep
          (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,false) <
          literalScore rep (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,true)) ≠
          bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 v then (1 : ℝ) else 0
    Integrable (fun s => ∑ v, C v s) μ ∧
      (∫ s, ∑ v, C v s ∂μ) ≤ (maxArity Γ * I.constraints.card : ℕ) *
        ((Real.log (Fintype.card (Literal V)) + 1) / bijunctiveRate rep ε) := by
  classical
  let μ := bijunctiveSeedMeasure rep I ε
  let C := fun (v : V) (s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) =>
      ∑ j : Fin I.constraints.card,
        if decide (literalScore rep
          (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,false) <
          literalScore rep (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,true)) ≠
          bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 v then (1 : ℝ) else 0
  let U := I.constraints.toFinset.biUnion (fun c => Finset.univ.image c.scope)
  let B := (Real.log (Fintype.card (Literal V)) + 1) / bijunctiveRate rep ε
  have hC (v : V) : Integrable (C v) μ ∧ (∫ s, C v s ∂μ) ≤ B :=
    expected_seed_graph_deletion_changes_bound rep I hI ε hε v
  have hzero (v : V) (hv : v ∉ U) : C v = 0 := by
    have hiso : ∀ c ∈ I.constraints, ∀ k : Fin c.rel.val.arity, c.scope k ≠ v := by
      intro c hc k hk
      apply hv
      apply Finset.mem_biUnion.mpr
      exact ⟨c,Multiset.mem_toFinset.mpr hc,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,hk⟩⟩
    funext s
    dsimp [C]
    apply Finset.sum_eq_zero
    intro j hj
    have hf := isolated_variable_graph_deletion_score_unchanged rep I
      (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) v hiso
      (fun i => decide (s.1 i ≤ 1 - ε/2) && decide (i ≠ j))
      (fun i => decide (s.1 i ≤ 1 - ε/2)) s.2.2 false
    have ht := isolated_variable_graph_deletion_score_unchanged rep I
      (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) v hiso
      (fun i => decide (s.1 i ≤ 1 - ε/2) && decide (i ≠ j))
      (fun i => decide (s.1 i ≤ 1 - ε/2)) s.2.2 true
    simp only [bijunctiveOutput, hf, ht, ne_eq, not_true_eq_false, ite_false]
  have hB : 0 ≤ B := by
    have hβ : 0 < bijunctiveRate rep ε := by
      unfold bijunctiveRate
      apply div_pos hε
      have hh : (0 : ℝ) < rep.clauseBound := by exact_mod_cast rep.clauseBound_pos
      positivity
    have hc : (1 : ℝ) ≤ Fintype.card (Literal V) := by
      exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Literal V))
    exact div_nonneg (by have h := Real.log_nonneg hc; linarith) (le_of_lt hβ)
  have hi : Integrable (fun s => ∑ v, C v s) μ := integrable_finset_sum _ (fun v _ => (hC v).1)
  refine ⟨hi,?_⟩
  rw [integral_finset_sum _ (fun v _ => (hC v).1)]
  have hsum : (∑ v : V, ∫ s, C v s ∂μ) = ∑ v ∈ U, ∫ s, C v s ∂μ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ U)
    intro v _ hv
    rw [hzero v hv]
    simp
  rw [hsum]
  calc
    (∑ v ∈ U, ∫ s, C v s ∂μ) ≤ (U.card : ℝ) * B := by
      simpa using Finset.sum_le_card_nsmul U (fun v => ∫ s, C v s ∂μ) B (fun v _ => (hC v).2)
    _ ≤ (maxArity Γ * I.constraints.card : ℕ) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast nonisolated_variables_bound I
