-- Prove2me | solution 1 for TheoryOfGames.SimpleGames.weights_wstar_iff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T08:01:20.390001+00:00
-- url     : https://prove2.me/submissions/109bb92e-76f0-44d5-8ee7-d76721377030

import Definitions.Def_TheoryOfGames_SimpleGames_Majority

/-!
# (50:B): weighted majorities satisfying (49:W*)

For nonnegative weights `w`, the system `weightedW w = {S | ½·∑w < ∑_{i∈S} wᵢ}` satisfies
(49:W*) exactly when the weights fulfil (50:B): every single weight lies in `[0, ½·∑w)` and
no coalition has exactly half the total weight.

Throughout, `W(S) := ∑_{i∈S} wᵢ`, so `W(S) + W(Sᶜ) = ∑_i wᵢ` and `½·∑w + ½·∑w = ∑w`.
The three clauses of (49:W*) translate as follows.

* **(49:W*:a)** `S ∈ W ↔ Sᶜ ∉ W` says `½ < W(S) ↔ W(Sᶜ) ≤ ½`, i.e.
  `½ < W(S) ↔ ½ ≤ W(S)` — which holds for all `S` *iff* `W(S) ≠ ½` for all `S` (that is
  (50:B:b)).
* **(49:W*:b)** upward closure is monotonicity of `W` under `w ≥ 0`.
* **(49:W*:c)** `I ∈ W` is `∑w > 0`, which follows from `w i₀ < ½·∑w` when `n ≥ 1`; when
  `n = 0` both sides of the equivalence are false, since `W(∅) = 0 = ½·∑w` violates (50:B:b).
  An `(n−1)`-element set has a singleton complement `{i₀}`, and membership reduces to
  `w i₀ < ½·∑w`, which is (50:B:a).
-/

open TheoryOfGames.SimpleGames

theorem solution {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    SatisfiesWStar (weightedW w) ↔ SatisfiesB w := by
  have keycompl : ∀ S : Finset (Fin n), ∑ i ∈ S, w i + ∑ i ∈ Sᶜ, w i = ∑ i, w i :=
    fun S => Finset.sum_add_sum_compl S (fun i => w i)
  have halfid : (1 / 2 : ℝ) * ∑ i, w i + (1 / 2 : ℝ) * ∑ i, w i = ∑ i, w i := by
    field_simp
    ring
  constructor
  · -- (49:W*) → (50:B)
    rintro ⟨ha, hb, hc⟩
    obtain ⟨huniv, hnminus⟩ := hc
    refine ⟨?_, ?_⟩
    · intro i₀
      refine ⟨hw i₀, ?_⟩
      have hcard : (Finset.univ \ {i₀}).card + 1 = n := by
        have hn : 0 < n := Nat.pos_of_ne_zero (by
          intro h0
          rw [h0] at i₀
          exact i₀.elim0)
        have hsub : ({i₀} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
        rw [Finset.card_sdiff_of_subset hsub, Finset.card_singleton, Finset.card_univ,
          Fintype.card_fin]
        omega
      have hwin : Finset.univ \ {i₀} ∈ weightedW w := hnminus _ hcard
      have hcompl : (Finset.univ \ {i₀})ᶜ = {i₀} := by
        ext i
        simp [Finset.mem_compl, Finset.mem_sdiff]
      have hsum : ∑ i ∈ Finset.univ \ {i₀}, w i = ∑ i, w i - w i₀ := by
        have h := keycompl (Finset.univ \ {i₀})
        rw [hcompl, Finset.sum_singleton] at h
        linarith
      simp only [weightedW, Set.mem_setOf_eq] at hwin
      rw [hsum] at hwin
      linarith
    · intro S
      by_contra hcon
      have hSnW : S ∉ weightedW w := by
        intro hmem
        simp only [weightedW, Set.mem_setOf_eq] at hmem
        linarith
      have hcompW : Sᶜ ∈ weightedW w := by
        by_contra hc2
        exact hSnW ((ha S).mpr hc2)
      simp only [weightedW, Set.mem_setOf_eq] at hcompW
      have h2 := keycompl S
      linarith
  · -- (50:B) → (49:W*)
    rintro ⟨hbound, hnotie⟩
    have hmono : ∀ S T' : Finset (Fin n), S ⊆ T' → ∑ i ∈ S, w i ≤ ∑ i ∈ T', w i := by
      intro S T' hsub
      have h := Finset.sum_sdiff (f := w) hsub
      have hnn : ∀ i ∈ T' \ S, (0 : ℝ) ≤ w i := fun i _ => hw i
      have hsumnn := Finset.sum_nonneg (f := w) hnn
      linarith
    refine ⟨?_, ?_, ?_⟩
    · intro S
      constructor
      · intro hS hcontra
        simp only [weightedW, Set.mem_setOf_eq] at hS hcontra
        have h2 := keycompl S
        linarith
      · intro hcontra
        simp only [weightedW, Set.mem_setOf_eq] at hcontra
        simp only [weightedW, Set.mem_setOf_eq]
        have h2 := keycompl S
        have hne := hnotie S
        by_cases hle2 : ∑ i ∈ S, w i ≤ (1 / 2 : ℝ) * ∑ i, w i
        · exact absurd (by linarith) hne
        · linarith
    · intro S T' hS hsub
      simp only [weightedW, Set.mem_setOf_eq] at hS ⊢
      exact lt_of_lt_of_le hS (hmono S T' hsub)
    · refine ⟨?_, ?_⟩
      · have hnne : Nonempty (Fin n) := by
          by_contra hcon
          have hempty : IsEmpty (Fin n) := not_nonempty_iff.mp hcon
          have h0 := hnotie ∅
          rw [Finset.sum_empty, Finset.univ_eq_empty] at h0
          norm_num at h0
        have i₀ := hnne.some
        have hlt := (hbound i₀).2
        have hsingleton : ∑ i ∈ ({i₀} : Finset (Fin n)), w i = w i₀ := Finset.sum_singleton w i₀
        have hTge : w i₀ ≤ ∑ i, w i := by
          have := hmono {i₀} Finset.univ (Finset.subset_univ _)
          rw [hsingleton] at this
          exact this
        have hw0 := hw i₀
        have hunivsum : ∑ i ∈ Finset.univ, w i = ∑ i, w i := rfl
        simp only [weightedW, Set.mem_setOf_eq]
        rw [hunivsum]
        linarith
      · intro S hcard
        have hcardc : Sᶜ.card = 1 := by
          rw [Finset.card_compl, Fintype.card_fin]
          omega
        obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hcardc
        simp only [weightedW, Set.mem_setOf_eq]
        have h2 := keycompl S
        rw [hi₀, Finset.sum_singleton] at h2
        have hlt := (hbound i₀).2
        linarith
