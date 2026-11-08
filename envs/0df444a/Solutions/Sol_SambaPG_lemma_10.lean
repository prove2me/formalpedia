-- Prove2me | solution 1 for SambaPG.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:02:37.247142+00:00
-- url     : https://prove2.me/submissions/3af1e354-4d63-4535-a76a-91575b6b9c89

import Mathlib
import Definitions.Def_SambaPG_sambaStep

open SambaPG in
theorem solution {A : Type*} [Fintype A] [DecidableEq A] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {p : A → ℝ} (hpos : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1) {ℓ : A} (hℓ : ∀ a, p a ≤ p ℓ)
    (i : A) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∀ a, 0 < sambaStep α p ℓ i x a) ∧ ∑ a, sambaStep α p ℓ i x a = 1 := by
  set u : A → ℝ := fun b =>
    p b + α * p b ^ 2 * ((if i = b then x / p b else 0) - (if i = ℓ then x / p ℓ else 0)) with hu
  have hS : sambaStep α p ℓ i x = fun a => if a = ℓ then 1 - ∑ b ∈ Finset.univ.erase ℓ, u b
      else u a := rfl
  have hps : ∑ b ∈ Finset.univ.erase ℓ, p b = 1 - p ℓ := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)]; ring
  obtain ⟨hx0, hx1⟩ := hx
  rw [hS]
  refine ⟨?_, ?_⟩
  · intro a
    by_cases hiℓ : i = ℓ
    · subst hiℓ
      have hu' : ∀ b, b ≠ i → u b = p b - α * p b ^ 2 * x / p i := by
        intro b hb
        simp only [u, if_neg (Ne.symm hb), eq_self_iff_true, ↓reduceIte]
        ring
      have hlt : ∀ b, α * p b ^ 2 * x / p i < p b := by
        intro b
        rw [div_lt_iff₀ (hpos i)]
        have h1 : p b ^ 2 * x ≤ p b * p i := by nlinarith [hpos b, hℓ b]
        nlinarith [mul_le_mul_of_nonneg_left h1 hα0.le, mul_pos (hpos b) (hpos i)]
      by_cases ha : a = i
      · simp only [if_pos ha]
        rw [Finset.sum_congr rfl (fun b hb => hu' b (Finset.ne_of_mem_erase hb)),
          Finset.sum_sub_distrib, hps]
        have : 0 ≤ ∑ b ∈ Finset.univ.erase i, α * p b ^ 2 * x / p i :=
          Finset.sum_nonneg (fun b _ => by
            have := hpos b; have := hpos i; positivity)
        linarith [hpos i]
      · simp only [if_neg ha]
        rw [hu' a ha]
        linarith [hlt a]
    · have hu' : ∀ b, u b = p b + if i = b then α * p i * x else 0 := by
        intro b
        simp only [u, if_neg hiℓ]
        split_ifs with h
        · subst h; have := (hpos i).ne'; field_simp <;> ring
        · ring
      by_cases ha : a = ℓ
      · simp only [if_pos ha]
        rw [Finset.sum_congr rfl (fun b _ => hu' b), Finset.sum_add_distrib, hps,
          Finset.sum_ite_eq, if_pos (Finset.mem_erase.mpr ⟨hiℓ, Finset.mem_univ i⟩)]
        have h1 : α * p i * x ≤ α * p ℓ := by
          have := hpos i
          nlinarith [mul_le_mul_of_nonneg_left (hℓ i) hα0.le, mul_pos hα0 (hpos i)]
        nlinarith [hpos ℓ]
      · simp only [if_neg ha]
        rw [hu' a]
        have := hpos a; have := hpos i
        split_ifs <;> positivity
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ), if_pos rfl]
    rw [Finset.sum_congr rfl (fun b hb => if_neg (Finset.ne_of_mem_erase hb))]
    ring
