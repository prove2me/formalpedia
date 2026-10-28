-- Prove2me | solution 1 for TheoryOfGames.ThreePerson.one_element_solution_iff_inessential
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:25:17.035506+00:00
-- url     : https://prove2.me/submissions/101deda9-8940-41c7-b005-8c2cd1ca551d

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

namespace Aux_TOG_one

open TheoryOfGames.CharFun

lemma sum_single_le {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (S : Finset (Fin n)) : ∑ k ∈ S, v {k} ≤ v S := by
  induction S using Finset.induction_on with
  | empty => simp [hv.1]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have h := hv.2.2 {a} S (Finset.disjoint_singleton_left.mpr ha)
    rw [Finset.singleton_union] at h
    linarith

lemma v_univ {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) :
    v Finset.univ = 0 := by
  have h := hv.2.1 ∅
  rw [Finset.compl_empty, hv.1] at h
  linarith

lemma iness_sigma {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) :
    IsInessential v ↔ ∑ j, v {j} = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have h0 := h {⟨0, hn⟩}
      unfold reducedForm at h0
      rw [Finset.sum_singleton] at h0
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have : (1 / (n : ℝ)) * ∑ j : Fin n, v {j} = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · simp [hn'] at h1
      · exact h1
  · intro hσ S
    have h1 := sum_single_le v hv S
    have h2 := sum_single_le v hv Sᶜ
    rw [hv.2.1 S] at h2
    have h3 := Finset.sum_add_sum_compl S (fun k => v {k})
    have hS : v S = ∑ k ∈ S, v {k} := by linarith
    unfold reducedForm
    rw [hσ, Finset.sum_add_distrib, hS]
    simp

end Aux_TOG_one

namespace Aux_TOG_one
open TheoryOfGames.ThreePerson
theorem dom_exists {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : TheoryOfGames.CharFun.IsCharFunction v) (hess : ¬ TheoryOfGames.CharFun.IsInessential v) (α : Fin n → ℝ)
    (hα : IsImputation v α) :
    ∃ β : Fin n → ℝ, IsImputation v β ∧ Dominates v β α ∧ ¬ Dominates v α β := by
  classical
  rw [Aux_TOG_one.iness_sigma v hv] at hess
  have hle : ∑ j, v {j} ≤ 0 := by
    have := Aux_TOG_one.sum_single_le v hv Finset.univ
    rwa [Aux_TOG_one.v_univ v hv] at this
  have hlt : ∑ j, v {j} < 0 := lt_of_le_of_ne hle hess
  -- some player gets strictly more than v{i}
  obtain ⟨i, hi⟩ : ∃ i, v {i} < α i := by
    by_contra hcon
    push_neg at hcon
    have : ∀ j, α j = v {j} := fun j => le_antisymm (hcon j) (hα.1 j)
    have h2 := hα.2
    simp only [this] at h2
    exact hess h2
  rcases n with _ | _ | n
  · exact i.elim0
  · exfalso
    have hu : ({0} : Finset (Fin 1)) = Finset.univ := by
      ext x; fin_cases x; simp
    rw [Fin.sum_univ_one, hu, Aux_TOG_one.v_univ v hv] at hlt
    exact lt_irrefl _ hlt
  · set d := α i - v {i} with hd
    have hdpos : 0 < d := by linarith
    have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    let β : Fin (n + 2) → ℝ := fun j => if j = i then v {i} else α j + d / ((n : ℝ) + 1)
    have hβi : β i = v {i} := by simp [β]
    have hβj : ∀ j, j ≠ i → β j = α j + d / ((n : ℝ) + 1) := fun j hj => by simp [β, hj]
    have hsumβ : ∑ j, β j = 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hβi]
      have h1 : ∑ j ∈ Finset.univ.erase i, β j =
          ∑ j ∈ Finset.univ.erase i, (α j + d / ((n : ℝ) + 1)) :=
        Finset.sum_congr rfl (fun j hj => hβj j (Finset.ne_of_mem_erase hj))
      rw [h1, Finset.sum_add_distrib, Finset.sum_erase_eq_sub (Finset.mem_univ i), hα.2,
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have : ((n + 2 - 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
        rw [show n + 2 - 1 = n + 1 by omega]; push_cast; ring
      rw [this, mul_div_cancel₀ _ hN.ne']
      rw [hd]; ring
    have hβimp : IsImputation v β := by
      refine ⟨fun j => ?_, hsumβ⟩
      by_cases hj : j = i
      · subst hj; rw [hβi]
      · rw [hβj j hj]
        have := hα.1 j
        have : 0 < d / ((n : ℝ) + 1) := div_pos hdpos hN
        linarith
    refine ⟨β, hβimp, ?_, ?_⟩
    · obtain ⟨j, hj⟩ := exists_ne i
      refine ⟨{i}ᶜ, ⟨j, by simp [hj]⟩, ?_, ?_⟩
      · unfold IsEffective
        have h1 := Finset.sum_compl_add_sum ({i} : Finset (Fin (n + 2))) β
        rw [Finset.sum_singleton, hsumβ, hβi] at h1
        rw [hv.2.1 {i}]
        linarith
      · intro k hk
        have hki : k ≠ i := by simpa using hk
        rw [hβj k hki]
        have : 0 < d / ((n : ℝ) + 1) := div_pos hdpos hN
        linarith
    · rintro ⟨S, ⟨k, hk⟩, heff, hlt2⟩
      have hS : ∀ j ∈ S, j = i := by
        intro j hj
        by_contra hji
        have h1 := hlt2 j hj
        rw [hβj j hji] at h1
        have : 0 < d / ((n : ℝ) + 1) := div_pos hdpos hN
        linarith
      have hSi : S = {i} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        exact ⟨hS k hk ▸ hk, hS⟩
      unfold IsEffective at heff
      rw [hSi, Finset.sum_singleton] at heff
      linarith

end Aux_TOG_one

open TheoryOfGames.ThreePerson in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : TheoryOfGames.CharFun.IsCharFunction v) :
    ((∃ α : Fin n → ℝ, IsSolution v {α}) ↔ TheoryOfGames.CharFun.IsInessential v) ∧
    (TheoryOfGames.CharFun.IsInessential v →
      ∃ α : Fin n → ℝ, ∀ V : Set (Fin n → ℝ), IsSolution v V ↔ V = {α}) := by
  have hirr : ∀ α : Fin n → ℝ, ¬ Dominates v α α := by
    rintro α ⟨S, ⟨k, hk⟩, _, h⟩
    exact lt_irrefl _ (h k hk)
  have hin_imp : TheoryOfGames.CharFun.IsInessential v →
      (IsImputation v (fun i => v {i}) ∧
        ∀ α' : Fin n → ℝ, IsImputation v α' → α' = fun i => v {i}) := by
    intro hin
    have hσ := (Aux_TOG_one.iness_sigma v hv).mp hin
    refine ⟨⟨fun i => le_refl _, hσ⟩, ?_⟩
    rintro α' ⟨h1, h2⟩
    have h3 : ∑ i, v {i} = ∑ i, α' i := by rw [hσ, h2]
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ => h1 i)).mp h3
    funext i
    exact (this i (Finset.mem_univ i)).symm
  have hsol : TheoryOfGames.CharFun.IsInessential v → IsSolution v {fun i => v {i}} := by
    intro hin
    obtain ⟨himp, huniq⟩ := hin_imp hin
    refine ⟨?_, ?_, ?_⟩
    · intro α hα; rw [Set.mem_singleton_iff.mp hα]; exact himp
    · intro α hα β hβ
      rw [Set.mem_singleton_iff.mp hα, Set.mem_singleton_iff.mp hβ]
      exact hirr _
    · intro β hβ hβV
      exact absurd (Set.mem_singleton_iff.mpr (huniq β hβ)) hβV
  refine ⟨⟨?_, fun hin => ⟨_, hsol hin⟩⟩, ?_⟩
  · rintro ⟨α, hint, _, hext⟩
    by_contra hess
    have hα : IsImputation v α := hint α (Set.mem_singleton α)
    obtain ⟨β, hβ, hdom, hndom⟩ := Aux_TOG_one.dom_exists v hv hess α hα
    have hne : β ∉ ({α} : Set (Fin n → ℝ)) := by
      intro h
      rw [Set.mem_singleton_iff.mp h] at hdom
      exact hirr _ hdom
    obtain ⟨α'', hα'', hd⟩ := hext β hβ hne
    rw [Set.mem_singleton_iff.mp hα''] at hd
    exact hndom hd
  · intro hin
    obtain ⟨himp, huniq⟩ := hin_imp hin
    refine ⟨fun i => v {i}, fun V => ⟨?_, ?_⟩⟩
    · rintro ⟨h1, _, h3⟩
      have hmem : (fun i => v {i}) ∈ V := by
        by_contra hnot
        obtain ⟨α, hαV, hd⟩ := h3 _ himp hnot
        rw [huniq α (h1 α hαV)] at hd
        exact hirr _ hd
      ext α
      constructor
      · intro hα
        exact Set.mem_singleton_iff.mpr (huniq α (h1 α hα))
      · intro hα
        rw [Set.mem_singleton_iff.mp hα]
        exact hmem
    · rintro rfl
      exact hsol hin
