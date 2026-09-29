-- Prove2me | solution 1 for ScenarioReduction.TernaryTree.card_IStarStar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T02:22:09.209677+00:00
-- url     : https://prove2.me/submissions/629ff934-2f82-4624-bae9-0e0751697eff

import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_IStarStar

open Finset
open ScenarioReduction.TernaryTree


/-- Counting core: for three distinct coordinates, filtering `Fin K → Fin n` by a predicate
that only looks at those three coordinates multiplies the number of admissible triples by
`n ^ (K - 3)`. -/
private theorem triple_card {K n : ℕ} [NeZero n] {a b c : Fin K}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Fin n → Fin n → Fin n → Prop) [DecidablePred fun t : Fin n × Fin n × Fin n =>
      p t.1 t.2.1 t.2.2] [∀ σ : Fin K → Fin n, Decidable (p (σ a) (σ b) (σ c))] :
    (univ.filter (fun σ : Fin K → Fin n => p (σ a) (σ b) (σ c))).card
      = (univ.filter (fun t : Fin n × Fin n × Fin n => p t.1 t.2.1 t.2.2)).card * n ^ (K - 3) := by
  classical
  -- the three coordinates form a 3-element set
  have hS : ({a, b, c} : Finset (Fin K)).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab, hac]), card_insert_of_notMem (by simp [hbc]),
      card_singleton]
  have hSle : ({a, b, c} : Finset (Fin K)).card ≤ Fintype.card (Fin K) := card_le_univ _
  have hK3 : 3 ≤ K := by simpa [hS] using hSle
  -- each fibre over an admissible triple has exactly `n ^ (K - 3)` elements
  have hfib : ∀ x y z : Fin n,
      (univ.filter (fun σ : Fin K → Fin n => σ a = x ∧ σ b = y ∧ σ c = z)).card
        = n ^ (K - 3) := by
    intro x y z
    set t : Fin K → Finset (Fin n) :=
      fun i => if i = a then {x} else if i = b then {y} else if i = c then {z} else univ with ht
    have hset : (univ.filter (fun σ : Fin K → Fin n => σ a = x ∧ σ b = y ∧ σ c = z))
        = Fintype.piFinset t := by
      ext σ
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, ht]
      constructor
      · rintro ⟨h1, h2, h3⟩ i
        by_cases hia : i = a
        · simp [hia, h1]
        · by_cases hib : i = b
          · simp [hia, hib, h2, Ne.symm hab]
          · by_cases hic : i = c
            · simp [hia, hib, hic, h3, Ne.symm hac, Ne.symm hbc]
            · simp [hia, hib, hic]
      · intro h
        refine ⟨?_, ?_, ?_⟩
        · have := h a; simpa using this
        · have := h b; simpa [Ne.symm hab] using this
        · have := h c; simpa [Ne.symm hac, Ne.symm hbc] using this
    rw [hset, Fintype.card_piFinset]
    have hsplit := Finset.prod_mul_prod_compl ({a, b, c} : Finset (Fin K)) (fun i => (t i).card)
    have h1 : ∏ i ∈ ({a, b, c} : Finset (Fin K)), (t i).card = 1 := by
      refine Finset.prod_eq_one ?_
      intro i hi
      simp only [mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · simp [ht]
      · simp [ht, Ne.symm hab]
      · simp [ht, Ne.symm hac, Ne.symm hbc]
    have h2 : ∏ i ∈ ({a, b, c} : Finset (Fin K))ᶜ, (t i).card = n ^ (K - 3) := by
      have : ∀ i ∈ ({a, b, c} : Finset (Fin K))ᶜ, (t i).card = n := by
        intro i hi
        simp only [mem_compl, mem_insert, mem_singleton, not_or] at hi
        simp [ht, hi.1, hi.2.1, hi.2.2]
      rw [Finset.prod_congr rfl this, Finset.prod_const, card_compl, hS]
      simp
    rw [← hsplit, h1, h2, one_mul]
  -- decompose the filter into those fibres
  have hmap : ∀ σ ∈ (univ.filter (fun σ : Fin K → Fin n => p (σ a) (σ b) (σ c))),
      (σ a, σ b, σ c) ∈ (univ.filter (fun t : Fin n × Fin n × Fin n => p t.1 t.2.1 t.2.2)) := by
    intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    exact hσ
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  have hcongr : ∀ w ∈ (univ.filter (fun t : Fin n × Fin n × Fin n => p t.1 t.2.1 t.2.2)),
      ((univ.filter (fun σ : Fin K → Fin n => p (σ a) (σ b) (σ c))).filter
        (fun σ => (σ a, σ b, σ c) = w)).card = n ^ (K - 3) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    rw [← hfib w.1 w.2.1 w.2.2]
    congr 1
    ext σ
    simp only [mem_filter, mem_univ, true_and, Prod.ext_iff]
    constructor
    · rintro ⟨-, h1, h2, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h1, h2, h3⟩
      rw [h1, h2, h3]; exact hw
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul]

theorem solution (K k0 : ℕ) (hk0 : 1 ≤ k0) (hk0K : k0 ≤ K - 2) (hK : 3 ≤ K) :
    (IStarStar K k0).card = 2 * 3 ^ (K - 2) ∧ (IStarStar K k0)ᶜ.card = 7 * 3 ^ (K - 2) := by
  classical
  have hk2 : k0 + 2 ≤ K := by omega
  set a : Fin K := ⟨k0 - 1, by omega⟩ with hadef
  set b : Fin K := ⟨k0, by omega⟩ with hbdef
  set c : Fin K := ⟨k0 + 1, by omega⟩ with hcdef
  have hab : a ≠ b := by
    simp only [hadef, hbdef, Ne, Fin.mk.injEq]; omega
  have hac : a ≠ c := by
    simp only [hadef, hcdef, Ne, Fin.mk.injEq]; omega
  have hbc : b ≠ c := by
    simp only [hbdef, hcdef, Ne, Fin.mk.injEq]; omega
  -- the unique `Fin K` index carrying paper level `l`
  have hmid : ∀ (σ : Fin K → Fin 3) (l : ℕ) (r : Fin K), r.val + 1 = l →
      (IsMid σ l ↔ σ r = 1) := by
    intro σ l r hr
    constructor
    · rintro ⟨r', hr', h'⟩
      have : r' = r := Fin.ext (by omega)
      rwa [this] at h'
    · intro h; exact ⟨r, hr, h⟩
  have houter : ∀ (σ : Fin K → Fin 3) (l : ℕ) (r : Fin K), r.val + 1 = l →
      (IsOuter σ l ↔ σ r ≠ 1) := by
    intro σ l r hr
    constructor
    · rintro ⟨r', hr', h'⟩
      have : r' = r := Fin.ext (by omega)
      rwa [this] at h'
    · intro h; exact ⟨r, hr, h⟩
  have ha0 : (a : Fin K).val + 1 = k0 := by simp only [hadef]; omega
  have hb0 : (b : Fin K).val + 1 = k0 + 1 := by simp only [hbdef]
  have hc0 : (c : Fin K).val + 1 = k0 + 2 := by simp only [hcdef]
  have hIS : IStarStar K k0
      = univ.filter (fun σ : Fin K → Fin 3 =>
          (σ a = 1 ∧ σ b ≠ 1 ∧ σ c ≠ 1) ∨ (σ a ≠ 1 ∧ σ b = 1 ∧ σ c = 1)) := by
    ext σ
    simp only [IStarStar, mem_filter, mem_univ, true_and,
      hmid σ k0 a ha0, hmid σ (k0 + 1) b hb0, hmid σ (k0 + 2) c hc0,
      houter σ k0 a ha0, houter σ (k0 + 1) b hb0, houter σ (k0 + 2) c hc0]
  have hmain : (IStarStar K k0).card = 6 * 3 ^ (K - 3) := by
    rw [hIS, triple_card hab hac hbc
      (fun x y z => (x = 1 ∧ y ≠ 1 ∧ z ≠ 1) ∨ (x ≠ 1 ∧ y = 1 ∧ z = 1))]
    norm_num
    decide
  have e1 : K - 2 = (K - 3) + 1 := by omega
  have e2 : K = (K - 3) + 3 := by omega
  have hp1 : (3 : ℕ) ^ (K - 2) = 3 ^ (K - 3) * 3 := by rw [e1, pow_succ]
  have hp2 : (3 : ℕ) ^ K = 3 ^ (K - 3) * 27 := by
    rw [e2, pow_add]; norm_num
  refine ⟨by omega, ?_⟩
  have hcard : Fintype.card (Fin K → Fin 3) = 3 ^ K := by simp
  rw [card_compl, hcard, hmain]
  omega
