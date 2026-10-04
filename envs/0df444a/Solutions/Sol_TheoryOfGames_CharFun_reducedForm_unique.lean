-- Prove2me | solution 1 for TheoryOfGames.CharFun.reducedForm_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:58:29.246105+00:00
-- url     : https://prove2.me/submissions/ab2e253b-fe27-40a7-a1c5-b14ece7f1fe3

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

set_option autoImplicit false

open TheoryOfGames.CharFun in
lemma rfu89_shift_isChar {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (α : Fin n → ℝ) (hα : ∑ k, α k = 0) :
    IsCharFunction (fun S => v S + ∑ k ∈ S, α k) := by
  obtain ⟨h0, hc, hs⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · simp [h0]
  · intro S
    have h1 := Finset.sum_compl_add_sum S α
    simp only
    rw [hc S]
    linarith
  · intro S T hST
    simp only
    rw [Finset.sum_union hST]
    have := hs S T hST
    linarith

open TheoryOfGames.CharFun in
lemma rfu89_alpha_sum {n : ℕ} (v : Finset (Fin n) → ℝ) :
    ∑ k : Fin n, (-v {k} + (1 / (n : ℝ)) * ∑ j : Fin n, v {j}) = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_neg_distrib, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
    ring

open TheoryOfGames.CharFun in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (w : Finset (Fin n) → ℝ) :
    (IsCharFunction w ∧ IsReduced w ∧ StrategicallyEquivalent v w) ↔ w = reducedForm v := by
  constructor
  · rintro ⟨_, hred, β, hβ, hw⟩
    have hk : ∀ k : Fin n, β k = -v {k} + (1 / (n : ℝ)) * ∑ j : Fin n, v {j} := by
      intro k
      have hsing : ∀ j : Fin n, w {j} = v {j} + β j := by
        intro j
        rw [hw {j}, Finset.sum_singleton]
      have hβ' : ∑ j : Fin n, β j = ∑ j : Fin n, (w {k} - v {j}) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hred k j, hsing j]
        ring
      rw [hβ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hβ'
      have hnpos : (0 : ℕ) < n := Fin.pos k
      have hn : (n : ℝ) ≠ 0 := by positivity
      have hwk : w {k} = (1 / (n : ℝ)) * ∑ j : Fin n, v {j} := by
        field_simp
        linarith
      have := hsing k
      linarith
    funext S
    rw [hw S]
    unfold reducedForm
    congr 1
    exact Finset.sum_congr rfl (fun k _ => hk k)
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · exact rfu89_shift_isChar v hv _ (rfu89_alpha_sum v)
    · intro j k
      simp only [reducedForm, Finset.sum_singleton]
      ring
    · exact ⟨_, rfu89_alpha_sum v, fun S => rfl⟩
