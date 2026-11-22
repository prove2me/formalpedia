-- Prove2me | solution 1 for RudinSquares.cor4_Q6_Q7_Q8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T18:38:11.54989+00:00
-- url     : https://prove2.me/submissions/fd6a8181-2c04-4e44-8f09-12fdd0f3c975
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RudinSquares_Defs
import Theorems.Thm_RudinSquares_prop3_four_subsets

namespace RudinSquares.Cor4Aux

open RudinSquares

abbrev Pat (s : Finset ℕ) : Prop :=
  (∃ t < 5, t ∈ s ∧ t + 1 ∈ s ∧ t + 2 ∈ s ∧ t + 3 ∈ s) ∨
  (∃ t < 4, t ∈ s ∧ t + 1 ∈ s ∧ t + 3 ∈ s ∧ t + 4 ∈ s) ∨
  (∃ t < 3, t ∈ s ∧ t + 1 ∈ s ∧ t + 4 ∈ s ∧ t + 5 ∈ s) ∨
  (∃ t < 3, t ∈ s ∧ t + 2 ∈ s ∧ t + 3 ∈ s ∧ t + 5 ∈ s) ∨
  (∃ t < 2, t ∈ s ∧ t + 1 ∈ s ∧ t + 5 ∈ s ∧ t + 6 ∈ s) ∨
  (∃ t < 2, t ∈ s ∧ t + 2 ∈ s ∧ t + 4 ∈ s ∧ t + 6 ∈ s)

set_option maxRecDepth 100000 in
theorem comb7 : ∀ s ∈ (Finset.range 7).powerset, 5 ≤ s.card → Pat s := by decide +kernel

set_option maxRecDepth 100000 in
theorem comb8 : ∀ s ∈ (Finset.range 8).powerset, 6 ≤ s.card → Pat s := by decide +kernel

/-- If `z I = 0`, no non-trivial progression has squares at all positions of `I`. -/
theorem noSq_of_z (I : Finset ℤ) (hz : z I = 0) (q a : ℤ) (hq : q ≠ 0)
    (h : ∀ i ∈ I, IsSq (q * i + a)) : False := by
  have hZ : Zset I = ∅ := Set.encard_eq_zero.1 hz
  have hg : 0 < Int.gcd q a := Int.gcd_pos_of_ne_zero_left a hq
  obtain ⟨r, s, hr, hs, hrs, hsf⟩ := Nat.sq_mul_squarefree_of_pos hg
  have ht : ((s : ℤ) * s) ∣ q ∧ ((s : ℤ) * s) ∣ a := by
    have h1 : ((s * s : ℕ) : ℤ) ∣ ((Int.gcd q a : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 ⟨r, by rw [← hrs]; ring⟩
    push_cast at h1
    exact ⟨h1.trans (Int.gcd_dvd_left _ _), h1.trans (Int.gcd_dvd_right _ _)⟩
  obtain ⟨⟨q1, rfl⟩, ⟨a1, rfl⟩⟩ := ht
  have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
  have hss : (s : ℤ) * s ≠ 0 := mul_ne_zero hs0 hs0
  have hmem : (q1, a1) ∈ Zset I := by
    refine ⟨?_, ?_, ?_⟩
    · have hgcd : Int.gcd ((s : ℤ) * s * q1) ((s : ℤ) * s * a1)
          = ((s : ℤ) * s).natAbs * Int.gcd q1 a1 := Int.gcd_mul_left _ _ _
      have hna : ((s : ℤ) * s).natAbs = s ^ 2 := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]; ring
      rw [hna, ← hrs] at hgcd
      have : Int.gcd q1 a1 = r :=
        (Nat.eq_of_mul_eq_mul_left (by positivity) hgcd).symm
      simpa [this] using hsf
    · rintro rfl; simp at hq
    · intro i hi
      obtain ⟨k, hk⟩ := h i hi
      have hdvd : (s : ℤ) ^ 2 ∣ k ^ 2 := ⟨q1 * i + a1, by rw [sq, sq, ← hk]; ring⟩
      obtain ⟨m, rfl⟩ := (Int.pow_dvd_pow_iff two_ne_zero).1 hdvd
      refine ⟨m, ?_⟩
      apply mul_left_cancel₀ hss
      linear_combination hk
  rw [hZ] at hmem
  exact hmem

theorem z0123 : z ({0, 1, 2, 3} : Finset ℤ) = 0 :=
  (prop3_four_subsets {0, 1, 2, 3} (by decide) (by decide)).1 (Or.inl (GenEq.refl _))
theorem z0134 : z ({0, 1, 3, 4} : Finset ℤ) = 0 :=
  (prop3_four_subsets {0, 1, 3, 4} (by decide) (by decide)).1
    (Or.inr (Or.inl (GenEq.refl _)))
theorem z0145 : z ({0, 1, 4, 5} : Finset ℤ) = 0 :=
  (prop3_four_subsets {0, 1, 4, 5} (by decide) (by decide)).1
    (Or.inr (Or.inr (Or.inl (GenEq.refl _))))
theorem z0235 : z ({0, 2, 3, 5} : Finset ℤ) = 0 :=
  (prop3_four_subsets {0, 2, 3, 5} (by decide) (by decide)).1
    (Or.inr (Or.inr (Or.inr (Or.inl (GenEq.refl _)))))
theorem z0156 : z ({0, 1, 5, 6} : Finset ℤ) = 0 :=
  (prop3_four_subsets {0, 1, 5, 6} (by decide) (by decide)).1
    (Or.inr (Or.inr (Or.inr (Or.inr (GenEq.refl _)))))

/-- A pattern `t + d * {i₀,i₁,i₂,i₃}` with `z {i₀,i₁,i₂,i₃} = 0` cannot be all squares. -/
theorem noPat (i₀ i₁ i₂ i₃ : ℤ) (hz : z ({i₀, i₁, i₂, i₃} : Finset ℤ) = 0)
    (q a : ℤ) (hq : q ≠ 0) (d t : ℤ) (hd : d ≠ 0)
    (h₀ : IsSq (q * (t + d * i₀) + a)) (h₁ : IsSq (q * (t + d * i₁) + a))
    (h₂ : IsSq (q * (t + d * i₂) + a)) (h₃ : IsSq (q * (t + d * i₃) + a)) : False := by
  refine noSq_of_z _ hz (q * d) (q * t + a) (mul_ne_zero hq hd) ?_
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · convert h₀ using 1; ring
  · convert h₁ using 1; ring
  · convert h₂ using 1; ring
  · convert h₃ using 1; ring

theorem not_pat (s : Finset ℕ) (q a : ℤ) (hq : q ≠ 0)
    (hs : ∀ n ∈ s, IsSq (q * (n : ℤ) + a)) (hp : Pat s) : False := by
  have H : ∀ n : ℕ, ∀ e : ℤ, (n : ℤ) = e → n ∈ s → IsSq (q * e + a) := by
    rintro n e rfl hn; exact hs n hn
  rcases hp with ⟨t, -, h0, h1, h2, h3⟩ | ⟨t, -, h0, h1, h2, h3⟩ | ⟨t, -, h0, h1, h2, h3⟩ |
      ⟨t, -, h0, h1, h2, h3⟩ | ⟨t, -, h0, h1, h2, h3⟩ | ⟨t, -, h0, h1, h2, h3⟩
  · exact noPat 0 1 2 3 z0123 q a hq 1 t one_ne_zero
      (H _ _ (by push_cast; ring) h0) (H _ _ (by push_cast; ring) h1)
      (H _ _ (by push_cast; ring) h2) (H _ _ (by push_cast; ring) h3)
  · exact noPat 0 1 3 4 z0134 q a hq 1 t one_ne_zero
      (H _ _ (by push_cast; ring) h0) (H _ _ (by push_cast; ring) h1)
      (H _ _ (by push_cast; ring) h2) (H _ _ (by push_cast; ring) h3)
  · exact noPat 0 1 4 5 z0145 q a hq 1 t one_ne_zero
      (H _ _ (by push_cast; ring) h0) (H _ _ (by push_cast; ring) h1)
      (H _ _ (by push_cast; ring) h2) (H _ _ (by push_cast; ring) h3)
  · exact noPat 0 2 3 5 z0235 q a hq 1 t one_ne_zero
      (H _ _ (by push_cast; ring) h0) (H _ _ (by push_cast; ring) h1)
      (H _ _ (by push_cast; ring) h2) (H _ _ (by push_cast; ring) h3)
  · exact noPat 0 1 5 6 z0156 q a hq 1 t one_ne_zero
      (H _ _ (by push_cast; ring) h0) (H _ _ (by push_cast; ring) h1)
      (H _ _ (by push_cast; ring) h2) (H _ _ (by push_cast; ring) h3)
  · exact noPat 0 1 2 3 z0123 q a hq 2 t two_ne_zero
      (H _ _ (by push_cast; ring) h0) (H _ _ (by push_cast; ring) h1)
      (H _ _ (by push_cast; ring) h2) (H _ _ (by push_cast; ring) h3)

open Classical in
theorem Qap_eq (N : ℕ) (q a : ℤ) :
    Qap N q a = ((Finset.range N).filter (fun n : ℕ => IsSq (q * (n : ℤ) + a))).card := by
  unfold Qap
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [SN, S, and_comm]

open Classical in
theorem Qap_le_7 (q a : ℤ) (hq : q ≠ 0) : Qap 7 q a ≤ 4 := by
  rw [Qap_eq]
  by_contra hc
  push Not at hc
  set s := (Finset.range 7).filter (fun n : ℕ => IsSq (q * (n : ℤ) + a))
  have hmem : s ∈ (Finset.range 7).powerset := Finset.mem_powerset.2 (Finset.filter_subset _ _)
  exact not_pat s q a hq (fun n hn => (Finset.mem_filter.1 hn).2) (comb7 s hmem hc)

open Classical in
theorem Qap_le_8 (q a : ℤ) (hq : q ≠ 0) : Qap 8 q a ≤ 5 := by
  rw [Qap_eq]
  by_contra hc
  push Not at hc
  set s := (Finset.range 8).filter (fun n : ℕ => IsSq (q * (n : ℤ) + a))
  have hmem : s ∈ (Finset.range 8).powerset := Finset.mem_powerset.2 (Finset.filter_subset _ _)
  exact not_pat s q a hq (fun n hn => (Finset.mem_filter.1 hn).2) (comb8 s hmem hc)

open Classical in
theorem Qap_le_6 (q a : ℤ) (hq : q ≠ 0) : Qap 6 q a ≤ 4 := by
  refine le_trans ?_ (Qap_le_7 q a hq)
  rw [Qap_eq, Qap_eq]
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨by omega, hn.2⟩

theorem sq24 (n k : ℕ) (h : 24 * n + 1 = k * k) : IsSq (24 * (n : ℤ) + 1) :=
  ⟨k, by exact_mod_cast h⟩

open Classical in
theorem Qap_24_ge (N : ℕ) (S0 : Finset ℕ) (hN : ∀ n ∈ S0, n < N)
    (hS : ∀ n ∈ S0, IsSq (24 * (n : ℤ) + 1)) : S0.card ≤ Qap N 24 1 := by
  rw [Qap_eq]
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨hN n hn, hS n hn⟩

theorem Q_eq (N c : ℕ) (hup : ∀ q a : ℤ, q ≠ 0 → Qap N q a ≤ c) (hlow : c ≤ Qap N 24 1) :
    Q N = c := by
  have hbdd : BddAbove {c : ℕ | ∃ q a : ℤ, q ≠ 0 ∧ Qap N q a = c} :=
    ⟨c, by rintro _ ⟨q, a, hq, rfl⟩; exact hup q a hq⟩
  apply le_antisymm
  · exact csSup_le ⟨_, 24, 1, by norm_num, rfl⟩ (by rintro _ ⟨q, a, hq, rfl⟩; exact hup q a hq)
  · exact le_trans hlow (le_csSup hbdd ⟨24, 1, by norm_num, rfl⟩)

theorem sq_0125 : ∀ n ∈ ({0, 1, 2, 5} : Finset ℕ), IsSq (24 * (n : ℤ) + 1) := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact sq24 0 1 rfl
  · exact sq24 1 5 rfl
  · exact sq24 2 7 rfl
  · exact sq24 5 11 rfl

theorem sq_01257 : ∀ n ∈ ({0, 1, 2, 5, 7} : Finset ℕ), IsSq (24 * (n : ℤ) + 1) := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact sq24 0 1 rfl
  · exact sq24 1 5 rfl
  · exact sq24 2 7 rfl
  · exact sq24 5 11 rfl
  · exact sq24 7 13 rfl

end RudinSquares.Cor4Aux

open RudinSquares RudinSquares.Cor4Aux in
theorem solution : RudinSquares.Q 6 = 4 ∧ RudinSquares.Q 7 = 4 ∧ RudinSquares.Q 8 = 5 := by
  refine ⟨Q_eq 6 4 Qap_le_6 ?_, Q_eq 7 4 Qap_le_7 ?_, Q_eq 8 5 Qap_le_8 ?_⟩
  · exact Qap_24_ge 6 {0, 1, 2, 5} (by decide) sq_0125
  · exact Qap_24_ge 7 {0, 1, 2, 5} (by decide) sq_0125
  · exact Qap_24_ge 8 {0, 1, 2, 5, 7} (by decide) sq_01257
