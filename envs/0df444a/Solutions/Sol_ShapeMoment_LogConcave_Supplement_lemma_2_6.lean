-- Prove2me | solution 1 for ShapeMoment.LogConcave.Supplement.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:17:43.795242+00:00
-- url     : https://prove2.me/submissions/4942170e-24f7-4755-a2be-ab018d6377e6

import Definitions.Def_ShapeMoment_LogConcave_Supplement_TailShape

open scoped BigOperators

open ShapeMoment
open ShapeMoment.LogConcave
open ShapeMoment.LogConcave.Supplement

theorem solution (n : ℕ) (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) :
    IsIFR x ↔ IsLCSeq (tail x) := by
      set T : ℕ → ℝ := ext (tail x) with hTdef
      have hXnn : ∀ j, 0 ≤ ext x j := by
        intro j; unfold ext; split_ifs
        · exact hx _
        · exact le_refl _
      have htailnn : ∀ j, 0 ≤ tail x j := by
        intro j; unfold tail
        apply Finset.sum_nonneg; intro k _; split_ifs
        · exact hx _
        · exact le_refl _
      have hT0 : ∀ j, 0 ≤ T j := by
        intro j; simp only [hTdef]; unfold ext; split_ifs
        · exact htailnn _
        · exact le_refl _
      let S : ℕ → ℝ := fun j => ∑ k : Fin n, if j ≤ k.val + 1 then x k else 0
      have hTS : ∀ j, 1 ≤ j → T j = S j := by
        intro j hj
        simp only [hTdef, S]; unfold ext
        split_ifs with h
        · unfold tail
          apply Finset.sum_congr rfl
          intro k _
          have : (⟨j - 1, by omega⟩ : Fin n) ≤ k ↔ j ≤ k.val + 1 := by
            rw [Fin.le_def]; simp only; omega
          simp only [this]
        · symm
          apply Finset.sum_eq_zero
          intro k _
          have : ¬ (j ≤ k.val + 1) := by have := k.isLt; omega
          simp [this]
      have hXsum : ∀ j, ext x j = ∑ k : Fin n, if k.val + 1 = j then x k else 0 := by
        intro j; unfold ext
        split_ifs with h
        · symm
          rw [Finset.sum_eq_single (⟨j - 1, by omega⟩ : Fin n)]
          · simp only; rw [if_pos (by omega)]
          · intro b _ hb
            have : ¬ (b.val + 1 = j) := by
              intro h2; apply hb; ext; simp only; omega
            simp [this]
          · intro h; exact absurd (Finset.mem_univ _) h
        · symm
          apply Finset.sum_eq_zero
          intro k _
          have : ¬ (k.val + 1 = j) := by have := k.isLt; omega
          simp [this]
      have hrec : ∀ j, 1 ≤ j → T j = ext x j + T (j + 1) := by
        intro j hj
        rw [hTS j hj, hTS (j+1) (by omega), hXsum]
        simp only [S]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        by_cases h1 : k.val + 1 = j
        · rw [if_pos (by omega), if_pos h1, if_neg (by omega)]; ring
        · by_cases h2 : j ≤ k.val + 1
          · rw [if_pos h2, if_neg h1, if_pos (by omega)]; ring
          · rw [if_neg h2, if_neg h1, if_neg (by omega)]; ring
      have hmono : ∀ j, 1 ≤ j → T (j + 1) ≤ T j := by
        intro j hj; rw [hrec j hj]; linarith [hXnn j]
      have hanti : ∀ d a, 1 ≤ a → T (a + d) ≤ T a := by
        intro d
        induction d with
        | zero => intro a _; simp
        | succ d ih =>
          intro a ha
          have := hmono (a + d) (by omega)
          have := ih a ha
          rw [show a + (d+1) = a + d + 1 by omega]; linarith
      have hzero : ∀ j, n < j → T j = 0 := by
        intro j hj; simp only [hTdef]; unfold ext; rw [dif_neg (by omega)]
      constructor
      · intro hI
        refine ⟨htailnn, ?_, ?_⟩
        · intro k j l hk hkj hjl hl hpos
          have hl0 : 0 < T l := by
            rcases (hT0 l).lt_or_eq with h | h
            · exact h
            · exfalso; change 0 < T k * T l at hpos; rw [← h] at hpos; simp at hpos
          have := hanti (l - j) j (by omega)
          rw [show j + (l - j) = l by omega] at this
          show 0 < T j
          linarith
        · intro j hj1 hjn
          show T (j-1) * T (j+1) ≤ T j ^ 2
          obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          rcases (hT0 (i+1)).lt_or_eq with h | h
          · have hi : T (i+1) ≤ T i := hmono i (by omega)
            have hI' := hI i (i+1) (by omega) (by omega) (by omega) h
            have e1 := hrec i (by omega)
            have e2 := hrec (i+1) (by omega)
            have hipos : 0 < T i := by linarith
            change ext x i / T i ≤ ext x (i+1) / T (i+1) at hI'
            rw [div_le_div_iff₀ hipos h] at hI'
            have : ext x i = T i - T (i+1) := by linarith
            have : ext x (i+1) = T (i+1) - T (i+1+1) := by linarith
            nlinarith
          · have h2 : T (i+1+1) = 0 := by
              have := hmono (i+1) (by omega); have := hT0 (i+1+1); linarith
            rw [h2, ← h]; simp
      · rintro ⟨_, _, hLC⟩
        have hstep : ∀ i, 1 ≤ i → i + 1 ≤ n → 0 < T (i+1) →
            T (i+2) / T (i+1) ≤ T (i+1) / T i := by
          intro i hi hin hpos
          have hipos : 0 < T i := lt_of_lt_of_le hpos (hmono i hi)
          rcases Nat.lt_or_ge (i+1) n with h | h
          · have := hLC (i+1) (by omega) h
            change T (i+1-1) * T (i+1+1) ≤ T (i+1) ^ 2 at this
            simp only [Nat.add_sub_cancel] at this
            rw [div_le_div_iff₀ hpos hipos]
            nlinarith
          · rw [hzero (i+2) (by omega), zero_div]
            exact div_nonneg (hT0 _) (hT0 _)
        have hchain : ∀ d j, 1 ≤ j → j + d ≤ n → 0 < T (j + d) →
            T (j + d + 1) / T (j + d) ≤ T (j + 1) / T j := by
          intro d
          induction d with
          | zero => intro j _ _ _; simp
          | succ d ih =>
            intro j hj hjd hpos
            have hprev : 0 < T (j + d) := lt_of_lt_of_le hpos (by
              have := hmono (j+d) (by omega); rw [show j + (d+1) = j + d + 1 by omega]; exact this)
            have h1 := ih j hj (by omega) hprev
            have h2 := hstep (j + d) (by omega) (by omega)
              (by rw [show j + d + 1 = j + (d+1) by omega]; exact hpos)
            rw [show j + (d+1) = j + d + 1 by omega, show j + d + 1 + 1 = j + d + 2 by omega]
            linarith
        intro j k hj hjk hkn hpos
        change 0 < T k at hpos
        change ext x j / T j ≤ ext x k / T k
        have hjpos : 0 < T j := by
          have := hanti (k - j) j hj; rw [show j + (k - j) = k by omega] at this; linarith
        have hc := hchain (k - j) j hj (by omega) (by rw [show j + (k - j) = k by omega]; exact hpos)
        rw [show j + (k - j) = k by omega] at hc
        have e1 : ext x j = T j - T (j+1) := by linarith [hrec j hj]
        have e2 : ext x k = T k - T (k+1) := by linarith [hrec k (by omega)]
        rw [e1, e2, sub_div, sub_div, div_self hjpos.ne', div_self hpos.ne']
        linarith
