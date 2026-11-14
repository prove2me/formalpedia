-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.bijunctive_occurrence_violation_seed_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:00:24.439539+00:00
-- url     : https://prove2.me/submissions/f5575652-d7b1-4ca0-9ead-3a73d6278f5c

import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_seed_is_probability
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_seed_occurrence_omission_probability
import Theorems.Thm_StabilityDichotomies_Bijunctive_retained_occurrence_clause_violation_seed_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_violated_constraint_has_nontaut_violated_clause
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (i : Fin I.constraints.card) :
    (bijunctiveSeedMeasure rep I ε
      {seed | ¬ (occurrenceAt I i).Satisfied (bijunctiveOutput rep I ε seed.1 seed.2.1 seed.2.2)}).toReal ≤ ε := by
  classical
  let μ := bijunctiveSeedMeasure rep I ε
  letI : IsProbabilityMeasure μ := bijunctive_seed_is_probability rep I ε hε
  let c := occurrenceAt I i
  let L := rep.clauses c.rel
  let β := bijunctiveRate rep ε
  let z := 1 - Real.exp (-β)
  let E := {seed : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) |
    ¬ c.Satisfied (bijunctiveOutput rep I ε seed.1 seed.2.1 seed.2.2)}
  let O := {seed : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) |
    1 - ε / 2 < seed.1 i}
  let C : Fin L.length → Set ((Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) := fun j =>
    {seed | seed.1 i ≤ 1 - ε / 2 ∧
      (substituteClause c (L.get j)).1 ≠ literalNeg (substituteClause c (L.get j)).2 ∧
      ¬ clauseSatisfied (bijunctiveOutput rep I ε seed.1 seed.2.1 seed.2.2) (substituteClause c (L.get j))}
  have hβ : 0 < β := by
    dsimp [β,bijunctiveRate]
    apply div_pos hε
    have hh : (0 : ℝ) < rep.clauseBound := by exact_mod_cast rep.clauseBound_pos
    positivity
  have hz : 0 ≤ z := by
    dsimp [z]
    have h := Real.exp_le_one_iff.mpr (show -β ≤ 0 by linarith)
    linarith
  have hcover : E ⊆ O ∪ ⋃ j, C j := by
    intro seed hv
    by_cases ho : 1 - ε / 2 < seed.1 i
    · exact Or.inl ho
    · right
      obtain ⟨q,hq,ht,hvcl⟩ := violated_constraint_has_nontaut_violated_clause rep c
        (bijunctiveOutput rep I ε seed.1 seed.2.1 seed.2.2) hv
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp hq
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      change seed.1 i ≤ 1 - ε / 2 ∧ (substituteClause c (L.get j)).1 ≠
        literalNeg (substituteClause c (L.get j)).2 ∧ ¬ clauseSatisfied
          (bijunctiveOutput rep I ε seed.1 seed.2.1 seed.2.2) (substituteClause c (L.get j))
      rw [hj]
      exact ⟨le_of_not_gt ho,ht,hvcl⟩
  have hO : μ.real O = ε / 2 := bijunctive_seed_occurrence_omission_probability rep I ε hε hε1 i
  have hC : ∀ j, μ.real (C j) ≤ z := by
    intro j
    by_cases ht : (substituteClause c (L.get j)).1 ≠ literalNeg (substituteClause c (L.get j)).2
    · have h := retained_occurrence_clause_violation_seed_bound rep I hI ε hε i (L.get j)
        (List.get_mem L j) ht
      have hsub : C j ⊆ {seed | seed.1 i ≤ 1 - ε / 2 ∧ ¬ clauseSatisfied
          (bijunctiveOutput rep I ε seed.1 seed.2.1 seed.2.2) (substituteClause c (L.get j))} := by
        intro seed hs
        exact ⟨hs.1,hs.2.2⟩
      have hm := measureReal_mono hsub (measure_ne_top μ _)
      exact hm.trans h
    · have he : C j = ∅ := by
        apply Set.Subset.antisymm ?_ (Set.empty_subset _)
        intro seed hs
        exact ht hs.2.1
      rw [he,measureReal_empty]
      exact hz
  have hbound : μ.real E ≤ ε / 2 + (L.length : ℝ) * z := by
    calc
      μ.real E ≤ μ.real (O ∪ ⋃ j, C j) := measureReal_mono hcover (measure_ne_top μ _)
      _ ≤ μ.real O + μ.real (⋃ j, C j) := measureReal_union_le _ _
      _ ≤ μ.real O + ∑ j, μ.real (C j) := by gcongr; exact measureReal_iUnion_fintype_le C
      _ ≤ ε / 2 + ∑ _j : Fin L.length, z := by rw [hO]; gcongr; exact hC _
      _ = ε / 2 + (L.length : ℝ) * z := by simp
  have hzβ : z ≤ β := by
    dsimp [z]
    have h := Real.add_one_le_exp (-β)
    linarith
  have hb : (0 : ℝ) < rep.clauseBound := by exact_mod_cast rep.clauseBound_pos
  have hL : (L.length : ℝ) ≤ rep.clauseBound := by exact_mod_cast rep.clauseBound_spec c.rel
  have hfinal : ε / 2 + (L.length : ℝ) * z ≤ ε := by
    have hmul : (L.length : ℝ) * z ≤ (rep.clauseBound : ℝ) * β := by
      calc
        _ ≤ (rep.clauseBound : ℝ) * z := mul_le_mul_of_nonneg_right hL hz
        _ ≤ (rep.clauseBound : ℝ) * β := mul_le_mul_of_nonneg_left hzβ (le_of_lt hb)
    have hid : (rep.clauseBound : ℝ) * β = ε / 2 := by
      dsimp [β,bijunctiveRate]
      field_simp
    linarith
  exact hbound.trans hfinal
