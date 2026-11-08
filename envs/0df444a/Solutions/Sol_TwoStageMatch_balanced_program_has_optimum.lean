-- Prove2me | solution 1 for TwoStageMatch.balanced_program_has_optimum
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:43:43.656078+00:00
-- url     : https://prove2.me/submissions/48a732d1-1fb9-44c2-a36b-f61290fc4945

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1

open TwoStageMatch in
theorem solution {D₁ D₂ S : Type*} [Fintype D₁] [Fintype S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hg : Continuous g) :
    ∃ x : D₁ → S → ℝ, IsOptimal I g x := by
  have hc2 : ∀ i j, IsClosed {x : D₁ → S → ℝ | ¬ I.E (Sum.inl i) j → x i j = 0} := by
    intro i j
    by_cases hE : I.E (Sum.inl i) j
    · have : {x : D₁ → S → ℝ | ¬ I.E (Sum.inl i) j → x i j = 0} = Set.univ := by
        ext x
        simp [hE]
      rw [this]
      exact isClosed_univ
    · have : {x : D₁ → S → ℝ | ¬ I.E (Sum.inl i) j → x i j = 0} = {x | x i j = 0} := by
        ext x
        simp [hE]
      rw [this]
      exact isClosed_eq (by fun_prop) continuous_const
  have hset : {x : D₁ → S → ℝ | IsFeasible I x} =
      ((⋂ i, ⋂ j, {x : D₁ → S → ℝ | 0 ≤ x i j}) ∩
        (⋂ i, ⋂ j, {x : D₁ → S → ℝ | ¬ I.E (Sum.inl i) j → x i j = 0})) ∩
      ((⋂ i, {x : D₁ → S → ℝ | ∑ j, x i j ≤ 1}) ∩ (⋂ j, {x : D₁ → S → ℝ | ∑ i, x i j ≤ 1})) := by
    ext x
    simp only [IsFeasible, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    tauto
  have hclosed : IsClosed {x : D₁ → S → ℝ | IsFeasible I x} := by
    rw [hset]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le continuous_const (by fun_prop)
    · exact isClosed_iInter fun i => isClosed_iInter fun j => hc2 i j
    · exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
    · exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  have hbox : IsCompact (Set.pi Set.univ fun _ : D₁ =>
      Set.pi Set.univ fun _ : S => Set.Icc (0:ℝ) 1) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hsub : {x : D₁ → S → ℝ | IsFeasible I x} ⊆
      Set.pi Set.univ fun _ : D₁ => Set.pi Set.univ fun _ : S => Set.Icc (0:ℝ) 1 := by
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i j
    exact ⟨hx.1 i j, le_trans (Finset.single_le_sum (fun j _ => hx.1 i j) (Finset.mem_univ j))
      (hx.2.2.1 i)⟩
  have hK : IsCompact {x : D₁ → S → ℝ | IsFeasible I x} := hbox.of_isClosed_subset hclosed hsub
  have hne : ({x : D₁ → S → ℝ | IsFeasible I x}).Nonempty :=
    ⟨0, fun _ _ => le_rfl, fun _ _ _ => rfl, fun _ => by simp, fun _ => by simp⟩
  have hcont : Continuous (objective I g) := by
    unfold objective
    fun_prop
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  exact ⟨x, hx, hmin⟩
