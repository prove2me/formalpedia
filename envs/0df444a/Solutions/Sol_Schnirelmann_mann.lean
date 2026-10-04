-- Prove2me | solution 1 for Schnirelmann.mann
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:02:36.015593+00:00
-- url     : https://prove2.me/submissions/659d8757-fc3d-469c-8559-ff67b3185a3d

import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Data.Nat.Count
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum

/-!
Mann's theorem on Schnirelmann density (Dyson's proof, h = 2 case).

References: H. B. Mann, Ann. of Math. 43 (1942), 523-527; F. J. Dyson, J. London Math. Soc. 20 (1945),
8-14; the proof structure follows M. B. Nathanson, "Additive number theory and the Dyson transform",
arXiv:2407.12253, Sections 3-5, specialised to two sets and the full sumset.

Convention: `N S m` counts the elements of `S` in `[0, m]` (so it includes `0` when `0 ∈ S`).
For sets containing `0` this is the usual counting function plus one, which removes every
off-by-one special case from the argument.
-/

open Pointwise Classical

namespace Mann

/-- Number of elements of `S` in `[0, m]`. -/
noncomputable def N (S : Set ℕ) (m : ℕ) : ℕ := Nat.count (· ∈ S) (m + 1)

lemma N_succ (S : Set ℕ) (m : ℕ) : N S (m + 1) = N S m + if m + 1 ∈ S then 1 else 0 := by
  unfold N; rw [Nat.count_succ]

lemma N_zero {S : Set ℕ} (h : 0 ∈ S) : N S 0 = 1 := by
  simp [N, Nat.count_one, h]

lemma N_zero_not {S : Set ℕ} (h : 0 ∉ S) : N S 0 = 0 := by
  simp [N, Nat.count_one, h]

lemma N_mono (S : Set ℕ) {m m' : ℕ} (h : m ≤ m') : N S m ≤ N S m' :=
  Nat.count_monotone _ (by omega)

lemma N_le_succ (S : Set ℕ) (m : ℕ) : N S m ≤ N S (m + 1) := N_mono S (by omega)

/-- No element of `S` in `(k, m]` means the counts agree. -/
lemma N_eq_of_no_elem (S : Set ℕ) {k m : ℕ} (hkm : k ≤ m)
    (h : ∀ j, k < j → j ≤ m → j ∉ S) : N S m = N S k := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    rw [N_succ, ih (fun j hj1 hj2 => h j hj1 (by omega))]
    have := h (m + 1) (by omega) le_rfl
    simp [this]

/-- If the count grows on `(k, m]` there is an element there. -/
lemma exists_of_N_lt {S : Set ℕ} {k m : ℕ} (h : N S k < N S m) :
    ∃ j, k < j ∧ j ≤ m ∧ j ∈ S := by
  by_contra hcon
  push Not at hcon
  have hkm : k ≤ m := by
    by_contra hh
    push Not at hh
    have := N_mono S hh.le
    omega
  have := N_eq_of_no_elem S hkm (fun j h1 h2 => hcon j h1 h2)
  omega

lemma N_mono_pred {S S' : Set ℕ} {m : ℕ} (h : ∀ j ≤ m, j ∈ S → j ∈ S') : N S m ≤ N S' m := by
  unfold N
  exact Nat.count_mono_left (p := (· ∈ S)) (q := (· ∈ S')) (fun k hk hk' => h k (by omega) hk')

/-- Interval counts are monotone under inclusion. -/
lemma N_interval_mono {S S' : Set ℕ} (hsub : ∀ j, j ∈ S → j ∈ S') {k m : ℕ} (hkm : k ≤ m) :
    N S m + N S' k ≤ N S' m + N S k := by
  induction m, hkm using Nat.le_induction with
  | base => omega
  | succ m hkm ih =>
    rw [N_succ, N_succ]
    by_cases h1 : m + 1 ∈ S
    · have h2 : m + 1 ∈ S' := hsub _ h1
      simp [h1, h2]; omega
    · by_cases h2 : m + 1 ∈ S' <;> simp [h1, h2] <;> omega

/-- `a + x` embeds `[0, m - b] ∩ A` into `[b, m] ∩ A`; this is the counting form of Lemma 6. -/
lemma N_shift {A : Set ℕ} {b m : ℕ} (hb : b ≤ m) (hb1 : 1 ≤ b)
    (h : ∀ a, a ≤ m - b → a ∈ A → b + a ∈ A) :
    N A (m - b) + N A (b - 1) ≤ N A m := by
  have e1 : N A m = Nat.count (· ∈ A) b + Nat.count (fun k => b + k ∈ A) (m - b + 1) := by
    unfold N
    rw [show m + 1 = b + (m - b + 1) by omega, Nat.count_add]
  have e2 : N A (b - 1) = Nat.count (· ∈ A) b := by
    unfold N; congr 1; omega
  have e3 : N A (m - b) ≤ Nat.count (fun k => b + k ∈ A) (m - b + 1) := by
    unfold N
    exact Nat.count_mono_left (p := (· ∈ A)) (q := fun k => b + k ∈ A)
      (fun k hk hk' => h k (by omega) hk')
  omega

/-! ### The Dyson transform -/

/-- The exceptional set `T`: `c ∈ B ∩ [1, n]` such that `(a₀, c)` is a Dyson pair. -/
def Tset (A B : Set ℕ) (n a₀ : ℕ) : Set ℕ :=
  {c | c ∈ B ∧ 1 ≤ c ∧ c ≤ n ∧ (c + a₀ ≤ n → c + a₀ ∉ A)}

/-- `A' = A ∪ (T + a₀)`. -/
def Aprime (A B : Set ℕ) (n a₀ : ℕ) : Set ℕ := A ∪ {x | a₀ ≤ x ∧ x - a₀ ∈ Tset A B n a₀}

/-- `B' = B \ T`. -/
def Bprime (A B : Set ℕ) (n a₀ : ℕ) : Set ℕ := {x | x ∈ B ∧ x ∉ Tset A B n a₀}

section Transform

variable {A B : Set ℕ} {n a₀ : ℕ}

lemma Tset_sub_B {c : ℕ} (h : c ∈ Tset A B n a₀) : c ∈ B := h.1

lemma zero_not_Tset : 0 ∉ Tset A B n a₀ := fun h => by have := h.2.1; omega

lemma zero_mem_Aprime (h0A : 0 ∈ A) : 0 ∈ Aprime A B n a₀ := Or.inl h0A

lemma zero_mem_Bprime (h0B : 0 ∈ B) : 0 ∈ Bprime A B n a₀ := ⟨h0B, zero_not_Tset⟩

lemma N_Bprime (h0B : 0 ∈ B) (m : ℕ) :
    N (Bprime A B n a₀) m + N (Tset A B n a₀) m = N B m := by
  induction m with
  | zero =>
    rw [N_zero (zero_mem_Bprime h0B), N_zero_not zero_not_Tset, N_zero h0B]
  | succ m ih =>
    rw [N_succ (Bprime A B n a₀), N_succ (Tset A B n a₀), N_succ B]
    by_cases hT : m + 1 ∈ Tset A B n a₀
    · have hB : m + 1 ∈ B := hT.1
      have hB' : m + 1 ∉ Bprime A B n a₀ := fun h => h.2 hT
      simp only [hT, hB, hB', if_true, if_false]; omega
    · by_cases hB : m + 1 ∈ B
      · have hB' : m + 1 ∈ Bprime A B n a₀ := ⟨hB, hT⟩
        simp only [hT, hB, hB', if_true, if_false]; omega
      · have hB' : m + 1 ∉ Bprime A B n a₀ := fun h => hB h.1
        simp only [hT, hB, hB', if_false]; omega

lemma not_mem_of_shift {x : ℕ} (hxn : x ≤ n) (hx : a₀ ≤ x)
    (hT : x - a₀ ∈ Tset A B n a₀) : x ∉ A := by
  have := hT.2.2.2 (by omega)
  rwa [show x - a₀ + a₀ = x by omega] at this

lemma N_Aprime (h0A : 0 ∈ A) (m : ℕ) (hm : m ≤ n) :
    N (Aprime A B n a₀) m = N A m + N (Tset A B n a₀) (m - a₀) := by
  induction m with
  | zero =>
    rw [N_zero (zero_mem_Aprime h0A), N_zero h0A, Nat.zero_sub, N_zero_not zero_not_Tset]
  | succ m ih =>
    have ih := ih (by omega)
    rw [N_succ (Aprime A B n a₀), N_succ A, ih]
    by_cases h : a₀ ≤ m
    · rw [show m + 1 - a₀ = (m - a₀) + 1 by omega, N_succ (Tset A B n a₀)]
      by_cases hT : (m - a₀ + 1) ∈ Tset A B n a₀
      · have hT' : (m + 1) - a₀ ∈ Tset A B n a₀ := by
          rwa [show m + 1 - a₀ = m - a₀ + 1 by omega]
        have hA : m + 1 ∉ A := not_mem_of_shift (by omega) (by omega) hT'
        have hA' : m + 1 ∈ Aprime A B n a₀ := Or.inr ⟨by omega, hT'⟩
        simp only [hT, hA, hA', if_true, if_false]; omega
      · have hT' : ¬ ((m + 1) - a₀ ∈ Tset A B n a₀) := by
          rwa [show m + 1 - a₀ = m - a₀ + 1 by omega]
        by_cases hA : m + 1 ∈ A
        · have hA' : m + 1 ∈ Aprime A B n a₀ := Or.inl hA
          simp only [hT, hA, hA', if_true, if_false]; omega
        · have hA' : m + 1 ∉ Aprime A B n a₀ := by
            rintro (h1 | ⟨_, h2⟩)
            · exact hA h1
            · exact hT' h2
          simp only [hT, hA, hA', if_false]; omega
    · have e1 : m + 1 - a₀ = 0 := by omega
      have e2 : m - a₀ = 0 := by omega
      rw [e1, e2]
      have hiff : m + 1 ∈ Aprime A B n a₀ ↔ m + 1 ∈ A := by
        constructor
        · rintro (h1 | ⟨_, h2⟩)
          · exact h1
          · rw [e1] at h2; exact absurd h2 zero_not_Tset
        · exact Or.inl
      by_cases hA : m + 1 ∈ A
      · simp only [hA, hiff.2 hA, if_true]; omega
      · simp only [hA, mt hiff.1 hA, if_false]; omega

lemma sumset_sub {p : ℕ} (hp1 : 1 ≤ p) (hpn : p ≤ n) (ha₀ : a₀ ∈ A)
    (h : p ∈ Aprime A B n a₀ + Bprime A B n a₀) : p ∈ A + B := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.1 h
  rcases hx with hxA | ⟨hax, hxT⟩
  · exact Set.mem_add.2 ⟨x, hxA, y, hy.1, rfl⟩
  · have hcB : x - a₀ ∈ B := hxT.1
    have hc1 : 1 ≤ x - a₀ := hxT.2.1
    by_cases hy0 : y = 0
    · subst hy0
      exact Set.mem_add.2 ⟨a₀, ha₀, x - a₀, hcB, by omega⟩
    · have hyB : y ∈ B := hy.1
      have hyn : y ≤ n := by omega
      have hyT : y ∉ Tset A B n a₀ := hy.2
      have hmem : y + a₀ ≤ n ∧ y + a₀ ∈ A := by
        by_contra hcon
        apply hyT
        refine ⟨hyB, by omega, hyn, fun hle hmem => hcon ⟨hle, hmem⟩⟩
      exact Set.mem_add.2 ⟨y + a₀, hmem.2, x - a₀, hcB, by omega⟩

end Transform

/-! ### Minimal shifts and Dyson's inequality for the transform -/

section Minimal

variable {A B : Set ℕ} {n a₀ : ℕ}

/-- `a₀` is the least shift admitting a Dyson pair. -/
def MinimalShift (A B : Set ℕ) (n a₀ : ℕ) : Prop :=
  ∀ a, a < a₀ → a ∈ A → ∀ c, c ∈ B → 1 ≤ c → c ≤ n → c + a ≤ n ∧ c + a ∈ A

lemma N_pos_of_mem {S : Set ℕ} {x : ℕ} (hx : x ∈ S) : 1 ≤ N S x := by
  have h : Nat.count (· ∈ S) x < Nat.count (· ∈ S) (x + 1) :=
    Nat.count_lt_count_succ_iff.2 hx
  unfold N
  have : Nat.count (· ∈ S) (x + 1) ≤ Nat.count (· ∈ S) (x + 1) := le_rfl
  omega

/-- Lemma 6 (counting form). -/
lemma lemma6 (hmin : MinimalShift A B n a₀) {m c : ℕ} (hcB : c ∈ B) (hc1 : 1 ≤ c)
    (hcm : c ≤ m) (hmn : m ≤ n) (hlt : m < c + a₀) :
    N A (m - c) + N A (c - 1) ≤ N A m := by
  apply N_shift hcm hc1
  intro a ha haA
  exact (hmin a (by omega) haA c hcB hc1 (by omega)).2

/-- Every `z < a₀` satisfies `δ z + 1 ≤ N A z` (so `A` is already dense below `a₀`). -/
lemma claim5 (hmin : MinimalShift A B n a₀) (h0A : 0 ∈ A) (h0B : 0 ∈ B) (ha₀n : a₀ ≤ n)
    {γ δ : ℝ} (hδγ : δ ≤ γ) (hδ1 : δ ≤ 1)
    (H : ∀ m ≤ n, γ * m + 2 ≤ (N A m : ℝ) + N B m) :
    ∀ z, z < a₀ → δ * z + 1 ≤ (N A z : ℝ) := by
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro hz
    rcases Nat.eq_zero_or_pos z with rfl | hzpos
    · simp [N_zero h0A]
    · by_contra hcon
      push Not at hcon
      have hH := H z (by omega)
      have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
      have hBz : (1 : ℝ) < N B z := by nlinarith
      have hB2 : 1 < N B z := by exact_mod_cast hBz
      obtain ⟨c, hc0, hcz, hcB⟩ : ∃ j, 0 < j ∧ j ≤ z ∧ j ∈ B := by
        apply exists_of_N_lt (S := B) (k := 0) (m := z)
        rw [N_zero h0B]; exact hB2
      have hL := lemma6 hmin hcB hc0 hcz (by omega) (by omega)
      have i1 := ih (z - c) (by omega) (by omega)
      have i2 := ih (c - 1) (by omega) (by omega)
      have e1 : ((z - c : ℕ) : ℝ) = (z : ℝ) - c := by rw [Nat.cast_sub hcz]
      have e2 : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by rw [Nat.cast_sub hc0]; simp
      have hL' : ((N A (z - c) : ℕ) : ℝ) + (N A (c - 1) : ℕ) ≤ (N A z : ℕ) := by exact_mod_cast hL
      rw [e1] at i1
      rw [e2] at i2
      nlinarith


/-- Theorem 6: the transform keeps the density hypothesis, with `δ = min 1 γ`. -/
lemma theorem6 (hmin : MinimalShift A B n a₀) (h0A : 0 ∈ A) (h0B : 0 ∈ B) (ha₀n : a₀ ≤ n)
    {γ δ : ℝ} (hδγ : δ ≤ γ) (hδ1 : δ ≤ 1)
    (H : ∀ m ≤ n, γ * m + 2 ≤ (N A m : ℝ) + N B m) :
    ∀ m ≤ n, δ * m + 2 ≤ (N (Aprime A B n a₀) m : ℝ) + N (Bprime A B n a₀) m := by
  intro m hm
  have c5 := claim5 hmin h0A h0B ha₀n hδγ hδ1 H
  have e1 := N_Aprime (B := B) (a₀ := a₀) h0A m hm
  have e2 := N_Bprime (A := A) (n := n) (a₀ := a₀) h0B m
  have hTmono : N (Tset A B n a₀) (m - a₀) ≤ N (Tset A B n a₀) m := N_mono _ (Nat.sub_le _ _)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  by_cases hcase : N (Tset A B n a₀) (m - a₀) = N (Tset A B n a₀) m
  · have hsum : N (Aprime A B n a₀) m + N (Bprime A B n a₀) m = N A m + N B m := by omega
    have hsum' : ((N (Aprime A B n a₀) m : ℕ) : ℝ) + (N (Bprime A B n a₀) m : ℕ)
        = (N A m : ℕ) + (N B m : ℕ) := by exact_mod_cast hsum
    have hh := H m hm
    nlinarith
  · have hlt : N (Tset A B n a₀) (m - a₀) < N (Tset A B n a₀) m := lt_of_le_of_ne hTmono hcase
    obtain ⟨c, hc1, hc2, hcT⟩ := exists_of_N_lt hlt
    have hex : ∃ b, b ∈ B ∧ m - a₀ < b := ⟨c, Tset_sub_B hcT, hc1⟩
    obtain ⟨b, ⟨hbB, hbk⟩, hbmin⟩ : ∃ b, (b ∈ B ∧ m - a₀ < b) ∧
        ∀ j, j < b → ¬ (j ∈ B ∧ m - a₀ < j) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
    have hbc : b ≤ c := by
      by_contra hcon
      exact hbmin c (by omega) ⟨Tset_sub_B hcT, hc1⟩
    have hbm : b ≤ m := le_trans hbc hc2
    have hb1 : 1 ≤ b := by omega
    have hNB : N B (b - 1) = N B (m - a₀) := by
      apply N_eq_of_no_elem B (by omega)
      intro j hj1 hj2 hjB
      exact hbmin j (by omega) ⟨hjB, hj1⟩
    have hI := N_interval_mono (S := Tset A B n a₀) (S' := B) (fun j hj => Tset_sub_B hj)
      (show m - a₀ ≤ m by omega)
    have hD : N A m + N B (b - 1) ≤ N (Aprime A B n a₀) m + N (Bprime A B n a₀) m := by omega
    have hL6 := lemma6 hmin hbB hb1 hbm hm (by omega : m < b + a₀)
    have h5 := c5 (m - b) (by omega)
    have hHb := H (b - 1) (by omega)
    have e3 : ((m - b : ℕ) : ℝ) = (m : ℝ) - b := by rw [Nat.cast_sub hbm]
    have e4 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by rw [Nat.cast_sub hb1]; simp
    rw [e3] at h5
    rw [e4] at hHb
    have hD' : ((N A m : ℕ) : ℝ) + (N B (b - 1) : ℕ)
        ≤ (N (Aprime A B n a₀) m : ℕ) + (N (Bprime A B n a₀) m : ℕ) := by exact_mod_cast hD
    have hL6' : ((N A (m - b) : ℕ) : ℝ) + (N A (b - 1) : ℕ) ≤ (N A m : ℕ) := by
      exact_mod_cast hL6
    have hb0 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    nlinarith [mul_nonneg (sub_nonneg.2 hδγ) (sub_nonneg.2 hb0)]

end Minimal

/-! ### The Dyson step and the induction -/

section Assembly

lemma exists_shift {A B : Set ℕ} {n : ℕ} (h0A : 0 ∈ A) (h0B : 0 ∈ B) (hB : 2 ≤ N B n) :
    ∃ a₀, a₀ ∈ A ∧ a₀ ≤ n ∧ ∃ c, c ∈ Tset A B n a₀ := by
  obtain ⟨c, hc0, hcn, hcB⟩ : ∃ c, 0 < c ∧ c ≤ n ∧ c ∈ B := by
    apply exists_of_N_lt (S := B) (k := 0) (m := n)
    rw [N_zero h0B]; omega
  by_contra hcon
  push Not at hcon
  have key : ∀ k : ℕ, k * c ∈ A ∧ k * c ≤ n := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using h0A, by simp⟩
    | succ k ih =>
      have hnot := hcon (k * c) ih.1 ih.2 c
      have hh : c + k * c ≤ n ∧ c + k * c ∈ A := by
        by_contra h'
        exact hnot ⟨hcB, hc0, hcn, fun hle hmem => h' ⟨hle, hmem⟩⟩
      have e : (k + 1) * c = c + k * c := by ring
      rw [e]; exact ⟨hh.2, hh.1⟩
  have := (key (n + 1)).2
  nlinarith

lemma dyson_step {A B : Set ℕ} (h0A : 0 ∈ A) (h0B : 0 ∈ B) {n : ℕ} {γ δ : ℝ}
    (hδγ : δ ≤ γ) (hδ1 : δ ≤ 1)
    (H : ∀ m ≤ n, γ * m + 2 ≤ (N A m : ℝ) + N B m) (hB : 2 ≤ N B n) :
    ∃ A' B' : Set ℕ, 0 ∈ A' ∧ 0 ∈ B' ∧ N B' n < N B n ∧
      (∀ m ≤ n, δ * m + 2 ≤ (N A' m : ℝ) + N B' m) ∧
      (∀ p, 1 ≤ p → p ≤ n → p ∈ A' + B' → p ∈ A + B) := by
  have hex := exists_shift h0A h0B hB
  obtain ⟨a₀, ha₀A, ha₀n, ⟨c₀, hc₀⟩, hmin⟩ :
      ∃ a₀, a₀ ∈ A ∧ a₀ ≤ n ∧ (∃ c, c ∈ Tset A B n a₀) ∧ MinimalShift A B n a₀ := by
    refine ⟨Nat.find hex, ?_⟩
    obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex
    refine ⟨h1, h2, h3, ?_⟩
    intro a ha haA c hcB hc1 hcn
    by_contra hcon
    have : ∃ c', c' ∈ Tset A B n a := ⟨c, hcB, hc1, hcn, fun hle hmem => hcon ⟨hle, hmem⟩⟩
    exact Nat.find_min hex ha ⟨haA, by omega, this⟩
  refine ⟨Aprime A B n a₀, Bprime A B n a₀, zero_mem_Aprime h0A, zero_mem_Bprime h0B, ?_,
    theorem6 hmin h0A h0B ha₀n hδγ hδ1 H, fun p hp1 hpn h => sumset_sub hp1 hpn ha₀A h⟩
  have e2 := N_Bprime (A := A) (n := n) (a₀ := a₀) h0B n
  have h1 : 1 ≤ N (Tset A B n a₀) c₀ := N_pos_of_mem hc₀
  have h2 : N (Tset A B n a₀) c₀ ≤ N (Tset A B n a₀) n := N_mono _ hc₀.2.2.1
  omega

/-- Dyson's inequality for two sets (the finite form of Mann's theorem). -/
theorem dyson_main {δ : ℝ} (hδ1 : δ ≤ 1) :
    ∀ (k : ℕ) (A B : Set ℕ) (n : ℕ) (γ : ℝ), 0 ∈ A → 0 ∈ B → δ ≤ γ → N B n ≤ k →
      (∀ m ≤ n, γ * m + 2 ≤ (N A m : ℝ) + N B m) → δ * n + 1 ≤ (N (A + B) n : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro A B n γ h0A h0B _ hk _
    have := N_pos_of_mem h0B
    have h2 := N_mono B (Nat.zero_le n)
    have h3 := N_zero h0B
    omega
  | succ k ih =>
    intro A B n γ h0A h0B hδγ hk H
    by_cases hB : 2 ≤ N B n
    · obtain ⟨A', B', h0A', h0B', hlt, H', hsub⟩ := dyson_step h0A h0B hδγ hδ1 H hB
      have := ih A' B' n δ h0A' h0B' le_rfl (by omega) H'
      have hmono : N (A' + B') n ≤ N (A + B) n := by
        apply N_mono_pred
        intro j _ hj
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · exact Set.mem_add.2 ⟨0, h0A, 0, h0B, rfl⟩
        · exact hsub j hj0 (by assumption) hj
      have hmono' : ((N (A' + B') n : ℕ) : ℝ) ≤ (N (A + B) n : ℕ) := by exact_mod_cast hmono
      linarith
    · have hB1 : N B n ≤ 1 := by omega
      have hAB : N A n ≤ N (A + B) n := by
        apply N_mono_pred
        intro j _ hj
        exact Set.mem_add.2 ⟨j, hj, 0, h0B, by simp⟩
      have hH := H n le_rfl
      have hAB' : ((N A n : ℕ) : ℝ) ≤ (N (A + B) n : ℕ) := by exact_mod_cast hAB
      have hB1' : ((N B n : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hB1
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith

end Assembly

/-! ### Mann's theorem for Schnirelmann density -/

lemma N_eq_card {S : Set ℕ} (h0 : 0 ∈ S) (m : ℕ) :
    N S m = (Finset.filter (· ∈ S) (Finset.Ioc 0 m)).card + 1 := by
  induction m with
  | zero => simp [N_zero h0]
  | succ m ih =>
    rw [N_succ, ih, Finset.card_filter, Finset.card_filter,
      Finset.sum_Ioc_succ_top (Nat.zero_le m)]
    split_ifs <;> omega

/-- **Mann's theorem** (the `α + β` theorem): Schnirelmann density is superadditive,
`σ(D + E) ≥ min 1 (σ D + σ E)` for sets of naturals containing `0`. -/
theorem mann (D E : Set ℕ) (hD : 0 ∈ D) (hE : 0 ∈ E) :
    min 1 (schnirelmannDensity D + schnirelmannDensity E) ≤ schnirelmannDensity (D + E) := by
  rw [le_schnirelmannDensity_iff]
  intro n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hn']
  have hH : ∀ m ≤ n, (schnirelmannDensity D + schnirelmannDensity E) * m + 2
      ≤ (N D m : ℝ) + N E m := by
    intro m _
    have h1 : schnirelmannDensity D * m ≤ (Finset.filter (· ∈ D) (Finset.Ioc 0 m)).card :=
      schnirelmannDensity_mul_le_card_filter
    have h2 : schnirelmannDensity E * m ≤ (Finset.filter (· ∈ E) (Finset.Ioc 0 m)).card :=
      schnirelmannDensity_mul_le_card_filter
    rw [N_eq_card hD, N_eq_card hE]
    push_cast
    nlinarith
  have := dyson_main (δ := min 1 (schnirelmannDensity D + schnirelmannDensity E))
    (min_le_left _ _) (N E n) D E n (schnirelmannDensity D + schnirelmannDensity E) hD hE
    (min_le_right _ _) le_rfl hH
  have hDE : (0 : ℕ) ∈ D + E := Set.mem_add.2 ⟨0, hD, 0, hE, rfl⟩
  rw [N_eq_card (S := D + E) hDE] at this
  push_cast at this
  linarith

end Mann

/-- The platform statement: Mann's `α + β` theorem. -/
theorem solution (D E : Set ℕ) (hD : 0 ∈ D) (hE : 0 ∈ E) :
    min 1 (schnirelmannDensity D + schnirelmannDensity E) ≤ schnirelmannDensity (D + E) :=
  Mann.mann D E hD hE
