-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.nested_bijunctive_subinstances
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:50:36.961421+00:00
-- url     : https://prove2.me/submissions/ccbad7f7-d4be-4d8d-b6c4-344e50391137

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem thinned_member {Γ : Language} {V : Type} (I : Instance Γ V)
    (mask : Fin I.constraints.card → Bool) (c : Constraint Γ V)
    (hc : c ∈ (thinnedInstance I mask).constraints) : c ∈ I.constraints := by
  simp only [thinnedInstance, Multiset.mem_coe, List.mem_map, List.mem_filter,
    List.mem_ofFn] at hc
  obtain ⟨⟨i,d⟩,⟨⟨j,hj⟩,hm⟩,hd⟩ := hc
  cases hj
  simp only [Prod.snd] at hd
  subst c
  simp only [occurrenceAt]
  exact Multiset.mem_toList.mp (List.get_mem _ _)

private theorem thinned_mask_mono {Γ : Language} {V : Type} (I : Instance Γ V)
    (small big : Fin I.constraints.card → Bool)
    (h : ∀ i, small i = true → big i = true) :
    ∀ c, c ∈ (thinnedInstance I small).constraints → c ∈ (thinnedInstance I big).constraints := by
  intro c hc
  simp only [thinnedInstance, Multiset.mem_coe, List.mem_map, List.mem_filter,
    List.mem_ofFn] at hc ⊢
  obtain ⟨⟨i,d⟩,⟨⟨j,hj⟩,hm⟩,hd⟩ := hc
  exact ⟨(i,d),⟨⟨j,hj⟩,h i hm⟩,hd⟩

theorem solution {Γ : Language} {V : Type}
    (I : Instance Γ V) (hI : Satisfiable I) (ε cutoff : ℝ)
    (priority : Fin I.constraints.card → ℝ) (hcut : 1 - ε / 2 ≤ cutoff) :
    let G := thinnedInstance I (fun i => decide (priority i ≤ 1 - ε / 2))
    let F := thinnedInstance I (fun i => decide (priority i ≤ cutoff))
    Satisfiable F ∧ (∀ c ∈ G.constraints, c ∈ F.constraints) ∧
      ∀ i, priority i ≤ 1 - ε / 2 → occurrenceAt I i ∈ G.constraints := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · obtain ⟨x,hx⟩ := hI
    exact ⟨x,fun c hc => hx c (thinned_member I _ c hc)⟩
  · apply thinned_mask_mono
    intro i hi
    apply of_decide_eq_true at hi
    apply decide_eq_true
    exact hi.trans hcut
  · intro i hi
    simp only [thinnedInstance, Multiset.mem_coe, List.mem_map, List.mem_filter, List.mem_ofFn]
    exact ⟨(i, occurrenceAt I i), ⟨⟨i,rfl⟩,by simpa using hi⟩,rfl⟩
