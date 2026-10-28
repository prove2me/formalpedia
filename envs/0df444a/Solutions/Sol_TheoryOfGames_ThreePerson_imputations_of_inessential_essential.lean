-- Prove2me | solution 1 for TheoryOfGames.ThreePerson.imputations_of_inessential_essential
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:59:07.905379+00:00
-- url     : https://prove2.me/submissions/39bdd910-7c7a-46dd-a1b9-117840dd3dd0

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

namespace Aux_TOG_imp_iness

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

end Aux_TOG_imp_iness

open TheoryOfGames.ThreePerson in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : TheoryOfGames.CharFun.IsCharFunction v) :
    (TheoryOfGames.CharFun.IsInessential v → ∀ α : Fin n → ℝ, IsImputation v α ↔ α = fun i => v {i}) ∧
    (¬ TheoryOfGames.CharFun.IsInessential v →
      {α : Fin n → ℝ | IsImputation v α}.Infinite ∧ ¬ IsImputation v (fun i => v {i})) := by
  rw [Aux_TOG_imp_iness.iness_sigma v hv]
  have hle : ∑ j, v {j} ≤ 0 := by
    have := Aux_TOG_imp_iness.sum_single_le v hv Finset.univ
    rwa [Aux_TOG_imp_iness.v_univ v hv] at this
  constructor
  · intro hσ α
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : ∑ i, v {i} = ∑ i, α i := by rw [hσ, h2]
      have := (Finset.sum_eq_sum_iff_of_le (fun i _ => h1 i)).mp h3
      funext i
      exact (this i (Finset.mem_univ i)).symm
    · rintro rfl
      exact ⟨fun i => le_refl _, hσ⟩
  · intro hσ
    refine ⟨?_, fun h => hσ h.2⟩
    have hlt : ∑ j, v {j} < 0 := lt_of_le_of_ne hle hσ
    rcases n with _ | _ | n
    · simp at hlt
    · exfalso
      have hu : ({0} : Finset (Fin 1)) = Finset.univ := by
        ext x; fin_cases x; simp
      rw [Fin.sum_univ_one, hu, Aux_TOG_imp_iness.v_univ v hv] at hlt
      exact lt_irrefl _ hlt
    · set c : ℝ := -∑ j, v {j} with hc
      have hcpos : 0 < c := by linarith
      let f : ℝ → (Fin (n + 2) → ℝ) := fun t i =>
        v {i} + (if i = 0 then t else 0) + (if i = 1 then c - t else 0)
      apply Set.infinite_of_injOn_mapsTo (f := f) (s := Set.Icc 0 c)
      · intro t _ t' _ htt
        have := congrFun htt 0
        simp [f] at this
        exact this
      · intro t ht
        refine ⟨fun i => ?_, ?_⟩
        · simp only [f]
          have h1 : (0 : ℝ) ≤ (if i = 0 then t else 0) := by split_ifs <;> linarith [ht.1]
          have h2 : (0 : ℝ) ≤ (if i = 1 then c - t else 0) := by split_ifs <;> linarith [ht.2]
          linarith
        · simp only [f]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
            Finset.sum_ite_eq']
          simp only [Finset.mem_univ, if_true]
          linarith
      · exact Set.Icc_infinite hcpos
