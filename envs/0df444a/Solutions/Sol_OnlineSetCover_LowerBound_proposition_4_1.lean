-- Prove2me | solution 1 for OnlineSetCover.LowerBound.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T16:04:23.227538+00:00
-- url     : https://prove2.me/submissions/e306d18b-ff1a-4c1a-bb56-99b9233daf5b

import Mathlib
import Definitions.Def_OnlineSetCover_LowerBound_Game
import Definitions.Def_OnlineSetCover_LowerBound_BitFamily



namespace OnlineSetCover.LowerBound

section G
variable {X : Type*} [DecidableEq X]

lemma osc_chosenFrom_append (A : OnlineAlg X) (σ τ h : List X) :
    chosenFrom A h (σ ++ τ) = chosenFrom A h σ ∪ chosenFrom A (h ++ σ) τ := by
  induction σ generalizing h with
  | nil => simp [chosenFrom]
  | cons a σ ih =>
    simp only [List.cons_append, chosenFrom, ih, List.append_assoc, List.nil_append,
      Finset.union_assoc]

lemma osc_chosen_snoc (A : OnlineAlg X) (σ : List X) (x : X) :
    chosen A (σ ++ [x]) = chosen A σ ∪ A σ x := by
  unfold chosen
  rw [osc_chosenFrom_append]
  simp [chosenFrom]

lemma osc_chosenFrom_sub (𝓕 : Finset (Finset X)) (A : OnlineAlg X) (hA : IsValid 𝓕 A)
    (σ h : List X) : chosenFrom A h σ ⊆ 𝓕 := by
  induction σ generalizing h with
  | nil => simp [chosenFrom]
  | cons a σ ih =>
    simp only [chosenFrom]
    exact Finset.union_subset (hA h a).1 (ih _)

lemma osc_chosen_sub (𝓕 : Finset (Finset X)) (A : OnlineAlg X) (hA : IsValid 𝓕 A)
    (σ : List X) : chosen A σ ⊆ 𝓕 := osc_chosenFrom_sub 𝓕 A hA σ []

end G

lemma osc_bits_exists (k : ℕ) (P : Fin k → Prop) [DecidablePred P] :
    ∃ j : Fin (2 ^ k), ∀ t : Fin k, j.val.testBit t.val = true ↔ P t := by
  let f : Fin (2 ^ k) → (Fin k → Bool) := fun j t => j.val.testBit t.val
  have hinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · exact congrFun hab ⟨i, hi⟩
    · push_neg at hi
      have ha : a.val < 2 ^ i := lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by norm_num) hi)
      have hb : b.val < 2 ^ i := lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by norm_num) hi)
      rw [Nat.testBit_eq_false_of_lt ha, Nat.testBit_eq_false_of_lt hb]
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp⟩
  obtain ⟨j, hj⟩ := hbij.2 (fun t => decide (P t))
  refine ⟨j, fun t => ?_⟩
  have := congrFun hj t
  simp only [f] at this
  rw [this]; simp

def oscPw (k : ℕ) (t : Fin k) : Fin (2 ^ k) := ⟨2 ^ t.val, Nat.pow_lt_pow_right (by norm_num) t.isLt⟩

lemma osc_pw_bit (k : ℕ) (t s : Fin k) : (oscPw k t).val.testBit s.val = true ↔ s = t := by
  simp [oscPw, Nat.testBit_two_pow, Fin.ext_iff, eq_comm]

lemma osc_bitSet_inj (k : ℕ) : Function.Injective (bitSet k) := by
  intro a b h
  have : oscPw k a ∈ bitSet k a := by
    simp [bitSet, (osc_pw_bit k a a).2 rfl]
  rw [h] at this
  simp only [bitSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact ((osc_pw_bit k a b).1 this).symm

lemma osc_bitFamily_card (k : ℕ) : (bitFamily k).card = k := by
  unfold bitFamily
  rw [Finset.card_image_of_injective _ (osc_bitSet_inj k)]
  simp

lemma osc_bit_step (k : ℕ) (A : OnlineAlg (Fin (2 ^ k)))
    (hA : IsValid (bitFamily k) A) (σ : List (Fin (2 ^ k)))
    (hP : ∀ y ∈ σ, ∀ t : Fin k, bitSet k t ∉ chosen A σ → y ∈ bitSet k t)
    (hlt : (chosen A σ).card < k) :
    ∃ x, (∀ y ∈ σ ++ [x], ∀ t : Fin k, bitSet k t ∉ chosen A (σ ++ [x]) → y ∈ bitSet k t) ∧
      (chosen A σ).card + 1 ≤ (chosen A (σ ++ [x])).card ∧
      ∃ t, ∀ y ∈ σ ++ [x], y ∈ bitSet k t := by
  have hsub := osc_chosen_sub _ A hA σ
  -- some unchosen bit set
  have hex : ∃ t : Fin k, bitSet k t ∉ chosen A σ := by
    by_contra hcon
    push_neg at hcon
    have : bitFamily k ⊆ chosen A σ := by
      intro S hS
      simp only [bitFamily, Finset.mem_image] at hS
      obtain ⟨t, _, rfl⟩ := hS
      exact hcon t
    have := Finset.card_le_card this
    rw [osc_bitFamily_card] at this; omega
  obtain ⟨t0, ht0⟩ := hex
  obtain ⟨x, hx⟩ := osc_bits_exists k (fun t => bitSet k t ∉ chosen A σ)
  have hxmem : ∀ t, x ∈ bitSet k t ↔ bitSet k t ∉ chosen A σ := by
    intro t; rw [← hx t]; simp [bitSet]
  have hsnoc := osc_chosen_snoc A σ x
  refine ⟨x, ?_, ?_, t0, ?_⟩
  · intro y hy t ht
    rw [hsnoc] at ht
    have ht' : bitSet k t ∉ chosen A σ := fun h => ht (Finset.mem_union_left _ h)
    rcases List.mem_append.1 hy with hy | hy
    · exact hP y hy t ht'
    · simp at hy; subst hy; exact (hxmem t).2 ht'
  · obtain ⟨S, hS, hxS⟩ := (hA σ x).2 ⟨bitSet k t0, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      (hxmem t0).2 ht0⟩
    have hSF := osc_chosen_sub _ A hA (σ ++ [x]) hS
    simp only [bitFamily, Finset.mem_image] at hSF
    obtain ⟨t, _, rfl⟩ := hSF
    have hnot : bitSet k t ∉ chosen A σ := (hxmem t).1 hxS
    have : insert (bitSet k t) (chosen A σ) ⊆ chosen A (σ ++ [x]) := by
      rw [Finset.insert_subset_iff]; refine ⟨hS, ?_⟩
      rw [hsnoc]; exact Finset.subset_union_left
    have := Finset.card_le_card this
    rw [Finset.card_insert_of_notMem hnot] at this
    exact this
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hP y hy t0 ht0
    · simp at hy; subst hy; exact (hxmem t0).2 ht0

/-- adversary for the bit family -/
lemma osc_bit_adv (k : ℕ) (A : OnlineAlg (Fin (2 ^ k)))
    (hA : IsValid (bitFamily k) A) :
    ∀ n ≤ k, ∃ σ : List (Fin (2 ^ k)),
      (∀ y ∈ σ, ∀ t : Fin k, bitSet k t ∉ chosen A σ → y ∈ bitSet k t) ∧
      (n ≤ (chosen A σ).card) ∧ (0 < n → σ ≠ [] ∧ ∃ t, ∀ y ∈ σ, y ∈ bitSet k t) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨[], by simp, by simp, by simp⟩
  | succ n ih =>
    intro hn
    obtain ⟨σ, hP, hc, hne⟩ := ih (by omega)
    by_cases hn0 : n = 0
    · subst hn0
      obtain ⟨x, h1, h2, h3⟩ := osc_bit_step k A hA [] (by simp) (by simp [chosen, chosenFrom]; omega)
      exact ⟨[] ++ [x], h1, by omega, fun _ => ⟨by simp, h3⟩⟩
    by_cases hfull : (chosen A σ).card = k
    · exact ⟨σ, hP, by omega, fun _ => hne (by omega)⟩
    · have hle : (chosen A σ).card ≤ k := by
        have := Finset.card_le_card (osc_chosen_sub _ A hA σ)
        rwa [osc_bitFamily_card] at this
      obtain ⟨x, h1, h2, h3⟩ := osc_bit_step k A hA σ hP (by omega)
      exact ⟨σ ++ [x], h1, by omega, fun _ => ⟨by simp, h3⟩⟩

theorem p41_core (k : ℕ) (hk : 0 < k) :
    (bitFamily k).card = k ∧
    (∀ A : OnlineAlg (Fin (2 ^ k)), IsValid (bitFamily k) A →
      ∃ σ : List (Fin (2 ^ k)), σ ≠ [] ∧
        (∃ S ∈ bitFamily k, ∀ x ∈ σ, x ∈ S) ∧ k ≤ cost A σ) ∧
    (∃ A : OnlineAlg (Fin (2 ^ k)), IsValid (bitFamily k) A ∧
      ∀ (σ : List (Fin (2 ^ k))) (C : Finset (Finset (Fin (2 ^ k)))),
        IsCoverOf (bitFamily k) C σ → cost A σ ≤ k * C.card) := by
  refine ⟨osc_bitFamily_card k, ?_, ?_⟩
  · intro A hA
    obtain ⟨σ, _, hc, hne⟩ := osc_bit_adv k A hA k le_rfl
    obtain ⟨h1, t, ht⟩ := hne hk
    exact ⟨σ, h1, ⟨bitSet k t, Finset.mem_image_of_mem _ (Finset.mem_univ _), ht⟩, hc⟩
  · refine ⟨fun _ _ => bitFamily k, ?_, ?_⟩
    · intro h x
      refine ⟨le_rfl, fun ⟨S, hS, hxS⟩ => ⟨S, ?_, hxS⟩⟩
      rw [osc_chosen_snoc]; exact Finset.mem_union_right _ hS
    · intro σ C hC
      have hle : cost (fun (_ : List (Fin (2 ^ k))) _ => bitFamily k) σ ≤ k := by
        unfold cost
        have := Finset.card_le_card (osc_chosenFrom_sub (bitFamily k)
          (fun (_ : List (Fin (2 ^ k))) _ => bitFamily k) (fun _ _ => ⟨le_rfl, fun ⟨S, hS, hxS⟩ =>
            ⟨S, by rw [osc_chosen_snoc]; exact Finset.mem_union_right _ hS, hxS⟩⟩) σ [])
        rwa [osc_bitFamily_card] at this
      rcases σ with _ | ⟨a, σ⟩
      · simp [cost, chosen, chosenFrom]
      · obtain ⟨S, hS, _⟩ := hC.2 a (by simp)
        have : 1 ≤ C.card := Finset.card_pos.2 ⟨S, hS⟩
        nlinarith
end OnlineSetCover.LowerBound

open OnlineSetCover.LowerBound


theorem solution (k : ℕ) (hk : 0 < k) :
    (bitFamily k).card = k ∧
    (∀ A : OnlineAlg (Fin (2 ^ k)), IsValid (bitFamily k) A →
      ∃ σ : List (Fin (2 ^ k)), σ ≠ [] ∧
        (∃ S ∈ bitFamily k, ∀ x ∈ σ, x ∈ S) ∧ k ≤ cost A σ) ∧
    (∃ A : OnlineAlg (Fin (2 ^ k)), IsValid (bitFamily k) A ∧
      ∀ (σ : List (Fin (2 ^ k))) (C : Finset (Finset (Fin (2 ^ k)))),
        IsCoverOf (bitFamily k) C σ → cost A σ ≤ k * C.card) := by
  exact p41_core k hk
