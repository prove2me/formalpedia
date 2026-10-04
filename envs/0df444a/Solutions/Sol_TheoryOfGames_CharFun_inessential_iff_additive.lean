-- Prove2me | solution 1 for TheoryOfGames.CharFun.inessential_iff_additive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:41:07.058038+00:00
-- url     : https://prove2.me/submissions/9d78c427-f68c-4070-a148-b300a422e7c4

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

set_option autoImplicit false

open TheoryOfGames.CharFun in
theorem additive_sum_singletons_3639b84e {n : ℕ} (v : Finset (Fin n) → ℝ) (h0 : v ∅ = 0)
    (h : ∀ S T : Finset (Fin n), Disjoint S T → v (S ∪ T) = v S + v T) :
    ∀ S : Finset (Fin n), v S = ∑ k ∈ S, v {k} := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp [h0]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.insert_eq]
    exact h {a} s (Finset.disjoint_singleton_left.mpr ha)

open TheoryOfGames.CharFun in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) :
    IsInessential v ↔ ∀ S T : Finset (Fin n), Disjoint S T → v (S ∪ T) = v S + v T := by
  obtain ⟨h0, hc, _⟩ := hv
  constructor
  · intro hi S T hST
    have key : ∀ U : Finset (Fin n), v U = -∑ k ∈ U, (-v {k} + (1 / (n : ℝ)) * ∑ j : Fin n, v {j}) := by
      intro U
      have := hi U
      unfold reducedForm at this
      linarith
    rw [key, key S, key T, Finset.sum_union hST]
    ring
  · intro hadd S
    have hs := additive_sum_singletons_3639b84e v h0 hadd
    have huniv : ∑ j : Fin n, v {j} = 0 := by
      have h1 := hs Finset.univ
      have h2 := hc ∅
      rw [Finset.compl_empty, h0, neg_zero] at h2
      rw [← h1, h2]
    unfold reducedForm
    rw [huniv, hs S, ← Finset.sum_add_distrib]
    simp
