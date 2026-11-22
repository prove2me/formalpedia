-- Prove2me | solution 1 for RudinSquares.recursion
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T17:34:50.169525+00:00
-- url     : https://prove2.me/submissions/04cecd41-cd10-48d9-afab-07f3cfd00380

import Mathlib
import Definitions.Def_RudinSquares_Defs

namespace RudinSquaresRecAux
open RudinSquares

lemma SN_finite (N : ℕ) (q a : ℤ) : (SN N q a).Finite :=
  (Set.finite_lt_nat N).subset Set.inter_subset_right

lemma qap_le (N : ℕ) (q a : ℤ) : Qap N q a ≤ N := by
  unfold Qap
  calc (SN N q a).ncard ≤ ({n : ℕ | n < N}).ncard :=
        Set.ncard_le_ncard Set.inter_subset_right (Set.finite_lt_nat N)
    _ = N := by
        rw [show ({n : ℕ | n < N} : Set ℕ) = ((Finset.range N : Finset ℕ) : Set ℕ) by
          ext; simp, Set.ncard_coe_finset, Finset.card_range]

lemma bdd (N : ℕ) : BddAbove {c : ℕ | ∃ q a : ℤ, q ≠ 0 ∧ Qap N q a = c} := by
  refine ⟨N, ?_⟩
  rintro c ⟨q, a, -, rfl⟩
  exact qap_le N q a

lemma le_Q (N : ℕ) (q a : ℤ) (hq : q ≠ 0) : Qap N q a ≤ Q N :=
  le_csSup (bdd N) ⟨q, a, hq, rfl⟩

lemma exists_Q (N : ℕ) : ∃ q a : ℤ, q ≠ 0 ∧ Qap N q a = Q N :=
  Nat.sSup_mem (s := {c : ℕ | ∃ q a : ℤ, q ≠ 0 ∧ Qap N q a = c})
    ⟨_, 1, 0, one_ne_zero, rfl⟩ (bdd N)

lemma qap_mono (N : ℕ) (q a : ℤ) : Qap N q a ≤ Qap (N + 1) q a := by
  unfold Qap
  refine Set.ncard_le_ncard ?_ (SN_finite _ q a)
  rintro n ⟨h1, h2⟩
  exact ⟨h1, by simp only [Set.mem_setOf_eq] at h2 ⊢; omega⟩

lemma qap_succ_le (N : ℕ) (q a : ℤ) : Qap (N + 1) q a ≤ Qap N q a + 1 := by
  unfold Qap
  calc (SN (N + 1) q a).ncard ≤ (insert N (SN N q a)).ncard := by
        refine Set.ncard_le_ncard ?_ ((SN_finite N q a).insert N)
        rintro n ⟨h1, h2⟩
        simp only [Set.mem_setOf_eq] at h2
        by_cases hn : n = N
        · exact Or.inl hn
        · exact Or.inr ⟨h1, by simp only [Set.mem_setOf_eq]; omega⟩
    _ ≤ (SN N q a).ncard + 1 := Set.ncard_insert_le _ _

/-- Dividing `(q, a)` by the largest square dividing `gcd(q, a)` gives a pair with squarefree
gcd that still takes squares at every point of `I`. -/
lemma reduce (q a : ℤ) (hq : q ≠ 0) (I : Finset ℤ) (h : ∀ i ∈ I, IsSq (q * i + a)) :
    (Zset I).Nonempty := by
  obtain ⟨s, b, hsb, hs⟩ := Nat.sq_mul_squarefree (Int.gcd q a)
  have hg : Int.gcd q a ≠ 0 := by
    intro h0; exact hq (Int.gcd_eq_zero_iff.mp h0).1
  have hb : (b : ℤ) ≠ 0 := by
    intro h0; apply hg; rw [← hsb]; simp at h0; simp [h0]
  have hm0 : (b : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hb
  have hmg : (b : ℤ) ^ 2 ∣ (Int.gcd q a : ℤ) := ⟨s, by rw [← hsb]; push_cast; ring⟩
  have hmq : (b : ℤ) ^ 2 ∣ q := hmg.trans (Int.gcd_dvd_left _ _)
  have hma : (b : ℤ) ^ 2 ∣ a := hmg.trans (Int.gcd_dvd_right _ _)
  obtain ⟨q', rfl⟩ := hmq
  obtain ⟨a', rfl⟩ := hma
  refine ⟨(q', a'), ?_, right_ne_zero_of_mul hq, ?_⟩
  · have h1 : Int.gcd ((b : ℤ) ^ 2 * q') ((b : ℤ) ^ 2 * a') = b ^ 2 * Int.gcd q' a' := by
      rw [Int.gcd_mul_left]; simp [Int.natAbs_pow]
    have hb' : b ^ 2 ≠ 0 := by
      intro h0; apply hb; simp at h0; simp [h0]
    have : s = Int.gcd q' a' := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hb')
      rw [hsb, h1]
    simpa [← this] using hs
  · intro i hi
    obtain ⟨k, hk⟩ := h i hi
    have hdk : (b : ℤ) ^ 2 ∣ k ^ 2 := ⟨q' * i + a', by rw [sq k, ← hk]; ring⟩
    rw [Int.pow_dvd_pow_iff two_ne_zero] at hdk
    obtain ⟨t, rfl⟩ := hdk
    refine ⟨t, ?_⟩
    apply mul_left_cancel₀ hm0
    linear_combination hk

end RudinSquaresRecAux

open RudinSquares RudinSquaresRecAux in
theorem solution (N : ℕ) :
    Q N ≤ Q (N + 1) ∧ Q (N + 1) ≤ Q N + 1 ∧
    (Q (N + 1) = Q N ↔
      ∀ I : Finset ℤ, I ⊆ Finset.Icc (0 : ℤ) (N : ℤ) → I.card = Q N + 1 → z I = 0) := by
  have h1 : Q N ≤ Q (N + 1) := by
    obtain ⟨q, a, hq, hQ⟩ := exists_Q N
    rw [← hQ]; exact (qap_mono N q a).trans (le_Q _ q a hq)
  have h2 : Q (N + 1) ≤ Q N + 1 := by
    obtain ⟨q, a, hq, hQ⟩ := exists_Q (N + 1)
    rw [← hQ]; exact (qap_succ_le N q a).trans (by have := le_Q N q a hq; omega)
  refine ⟨h1, h2, ⟨?_, ?_⟩⟩
  · intro h I hI hc
    by_contra hz
    have hne : (Zset I).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]; intro he; exact hz (by simp [z, he])
    obtain ⟨⟨q, a⟩, -, hq, hsq⟩ := hne
    have hJc : (I.image Int.toNat).card = I.card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy hxy
      have hx0 := (Finset.mem_Icc.mp (hI hx)).1
      have hy0 := (Finset.mem_Icc.mp (hI hy)).1
      omega
    have hsub : ((I.image Int.toNat : Finset ℕ) : Set ℕ) ⊆ SN (N + 1) q a := by
      intro n hn
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hn
      obtain ⟨i, hi, rfl⟩ := hn
      have hi' := Finset.mem_Icc.mp (hI hi)
      have hc : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi'.1
      refine ⟨?_, ?_⟩
      · show IsSq (q * ((i.toNat : ℕ) : ℤ) + a)
        rw [hc]; exact hsq i hi
      · simp only [Set.mem_setOf_eq]; omega
    have := Set.ncard_le_ncard hsub (SN_finite _ q a)
    rw [Set.ncard_coe_finset, hJc, hc] at this
    have := le_Q (N + 1) q a hq
    unfold Qap at this
    omega
  · intro h
    by_contra hne
    have hQ1 : Q (N + 1) = Q N + 1 := by omega
    obtain ⟨q, a, hq, hQ⟩ := exists_Q (N + 1)
    set F := (SN_finite (N + 1) q a).toFinset
    have hF : F.card = Q N + 1 := by
      rw [← hQ1, ← hQ]; unfold Qap; rw [Set.ncard_eq_toFinset_card _ (SN_finite (N + 1) q a)]
    have hIc : (F.image (Nat.cast : ℕ → ℤ)).card = Q N + 1 := by
      rw [Finset.card_image_of_injective _ Nat.cast_injective, hF]
    have hIs : F.image (Nat.cast : ℕ → ℤ) ⊆ Finset.Icc (0 : ℤ) (N : ℤ) := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      have hn' : n ∈ SN (N + 1) q a := (Set.Finite.mem_toFinset _).mp hn
      have : n < N + 1 := hn'.2
      simp only [Finset.mem_Icc]; omega
    have hz := h _ hIs hIc
    obtain ⟨p, hp⟩ := reduce q a hq (F.image (Nat.cast : ℕ → ℤ)) (by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      exact ((Set.Finite.mem_toFinset _).mp hn).1)
    have : Zset (F.image (Nat.cast : ℕ → ℤ)) = ∅ := Set.encard_eq_zero.mp hz
    rw [this] at hp
    exact hp
