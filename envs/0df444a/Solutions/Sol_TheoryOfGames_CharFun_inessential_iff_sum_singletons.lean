-- Prove2me | solution 1 for TheoryOfGames.CharFun.inessential_iff_sum_singletons
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:32:14.585737+00:00
-- url     : https://prove2.me/submissions/b1a40c7d-94c6-430f-bce3-732dcea6e3ed

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

set_option autoImplicit false

namespace FD7E9461

open TheoryOfGames.CharFun

lemma sum_le {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) (S : Finset (Fin n)) :
    ∑ k ∈ S, v {k} ≤ v S := by
  obtain ⟨h0, -, hsup⟩ := hv
  induction S using Finset.induction_on with
  | empty => simp [h0]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have hd : Disjoint ({a} : Finset (Fin n)) S := Finset.disjoint_singleton_left.mpr ha
    have := hsup {a} S hd
    rw [← Finset.insert_eq] at this
    linarith

lemma sigma_le {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) :
    ∑ j : Fin n, v {j} ≤ 0 := by
  have h1 := sum_le v hv Finset.univ
  have hu : v Finset.univ = 0 := by
    have := hv.2.1 ∅
    rw [Finset.compl_empty, hv.1] at this
    simpa using this
  linarith

lemma iness_iff {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) :
    IsInessential v ↔ ∑ j : Fin n, v {j} = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have := h {⟨0, hn⟩}
      unfold reducedForm at this
      simp only [Finset.sum_singleton] at this
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have : (1 / (n : ℝ)) * ∑ j : Fin n, v {j} = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · simp [hn'] at h1
      · exact h1
  · intro hs S
    unfold reducedForm
    rw [hs, mul_zero, Finset.sum_add_distrib, Finset.sum_const_zero, add_zero,
      Finset.sum_neg_distrib]
    have h1 := sum_le v hv S
    have h2 := sum_le v hv Sᶜ
    have h3 := hv.2.1 S
    have h4 : ∑ k ∈ S, v {k} + ∑ k ∈ Sᶜ, v {k} = ∑ j : Fin n, v {j} :=
      Finset.sum_add_sum_compl S _
    linarith

end FD7E9461

open TheoryOfGames.CharFun in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsCharFunction v) :
    (IsInessential v ↔ ∑ j : Fin n, v {j} = 0) ∧
      (IsEssential v ↔ ∑ j : Fin n, v {j} < 0) := by
  refine ⟨FD7E9461.iness_iff v hv, ?_⟩
  unfold IsEssential
  rw [FD7E9461.iness_iff v hv]
  have := FD7E9461.sigma_le v hv
  constructor
  · intro h; exact lt_of_le_of_ne this h
  · intro h; exact ne_of_lt h
