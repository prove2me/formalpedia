-- Prove2me | solution 1 for SeqLoss.FixedFraction.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:13:29.659572+00:00
-- url     : https://prove2.me/submissions/36f7dd60-c604-4d65-9d87-f4f3c7cd9f16

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

set_option autoImplicit false
open SeqLoss.FixedFraction

theorem slf_isLoss_elem (n : ℕ) : IsLoss (elem n) := by
  intro i; unfold elem; split_ifs <;> norm_num

theorem slf_sum_elem (n : ℕ) (hn : 1 ≤ n) : ∑ i, elem n i = 1 := by
  rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
  · simp [elem]; omega
  · intro j _ hj
    have : j.val ≠ n - 1 := fun h => hj (Fin.ext h)
    unfold elem
    rw [if_neg (by omega)]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem slf_phi2_e3 (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hmp : MergingProof φ) : φ 3 (elem 3) 1 = 0 := by
  obtain ⟨h1, h2⟩ := hmp
  have e3 := (hφ 3 (elem 3) (slf_isLoss_elem 3)).1
  have e2 := (hφ 2 (elem 2) (slf_isLoss_elem 2)).1
  obtain ⟨nn3, -, t3⟩ := e3
  obtain ⟨nn2, -, t2⟩ := e2
  rw [slf_sum_elem 3 (by norm_num), Fin.sum_univ_three] at t3
  rw [slf_sum_elem 2 (by norm_num), Fin.sum_univ_two] at t2
  have a0 := nn3 0
  have a1 := nn3 1
  have a2 := nn3 2
  exact le_antisymm (by linarith) a1

/-- first-component of `e_m` is non-increasing in m (for m ≥ 3 index 1 goes down) -/
theorem slf_B (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) :
    ∀ m : ℕ, 3 ≤ m → ∀ i : Fin m, i.val = 1 → φ m (elem m) i ≤ 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro i hi
    have : i = 1 := Fin.ext (by simpa using hi)
    subst this
    exact (slf_phi2_e3 φ hφ hmp).le
  | succ m hm ih =>
    intro i hi
    have h := (hpm m 2 (by norm_num) (by omega) ⟨1, by omega⟩ ⟨m - 1, by omega⟩ (by simp) (by simp; omega)).1
    have hi' : i = (⟨1, by omega⟩ : Fin m).castSucc := Fin.ext (by simpa using hi)
    rw [hi']
    exact h.trans (ih ⟨1, by omega⟩ rfl)

theorem slf_C (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hpm : PopulationMonotone φ)
    (n : ℕ) (k : Fin n) (hk : 1 ≤ k.val) :
    φ (n + 1) (elem (n + 1)) k.succ ≤ φ n (elem n) k := by
  have hn : 1 < n := by have := k.isLt; omega
  exact (hpm n 1 le_rfl hn ⟨0, by omega⟩ k (by simp) (by omega)).2

theorem slf_inter (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) :
    ∀ (n : ℕ) (i : Fin n), 1 ≤ i.val → i.val + 1 < n → φ n (elem n) i = 0 := by
  have S : ∀ c n : ℕ, ∀ i : Fin (n + 1), i.val = c + 1 → i.val + 1 < n + 1 →
      φ (n + 1) (elem (n + 1)) i ≤ 0 := by
    intro c
    induction c with
    | zero =>
      intro n i hi hin
      exact slf_B φ hφ hpm hmp (n + 1) (by omega) i hi
    | succ c ih =>
      intro n i hi hin
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hk : c + 1 < n' + 1 := by omega
      have hi' : i = (⟨c + 1, hk⟩ : Fin (n' + 1)).succ := Fin.ext (by simpa using hi)
      rw [hi']
      refine (slf_C φ hpm (n' + 1) ⟨c + 1, hk⟩ (by simp)).trans ?_
      exact ih n' ⟨c + 1, hk⟩ rfl (by simp; omega)
  intro n i h1 h2
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, i.val = c + 1 := ⟨i.val - 1, by omega⟩
  exact le_antisymm (S c n' i hc h2) ((hφ _ (elem _) (slf_isLoss_elem _)).1.1 i)
theorem slf_ab_sum (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) (n : ℕ) (hn : 2 ≤ n) :
    φ n (elem n) ⟨0, by omega⟩ + φ n (elem n) ⟨n - 1, by omega⟩ = 1 := by
  have t := (hφ n (elem n) (slf_isLoss_elem n)).1.2.2
  rw [slf_sum_elem n (by omega)] at t
  rw [← t]
  symm
  apply Finset.sum_eq_add (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n)
  · intro h; have := congrArg Fin.val h; simp at this; omega
  · intro c _ hc
    apply slf_inter φ hφ hpm hmp
    · by_contra hcon
      apply hc.1
      exact Fin.ext (by simp; omega)
    · by_contra hcon
      apply hc.2
      exact Fin.ext (by simp; omega)
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

theorem slf_endpoints (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) (n : ℕ) (hn : 2 ≤ n) :
    φ n (elem n) ⟨0, by omega⟩ = φ 2 (elem 2) 0 ∧
    φ n (elem n) ⟨n - 1, by omega⟩ = φ 2 (elem 2) 1 := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ n hn ih =>
    have h1 := (hpm n 1 le_rfl (by omega) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ (by simp) (by simp; omega)).1
    have h2 := (hpm n 1 le_rfl (by omega) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ (by simp) (by simp; omega)).2
    have s1 := slf_ab_sum φ hφ hpm hmp n hn
    have s2 := slf_ab_sum φ hφ hpm hmp (n + 1) (by omega)
    have e1 : (⟨0, by omega⟩ : Fin (n + 1)) = (⟨0, by omega⟩ : Fin n).castSucc := rfl
    have e2 : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = (⟨n - 1, by omega⟩ : Fin n).succ :=
      Fin.ext (by simp; omega)
    rw [e1] at s2 ⊢
    rw [e2] at s2 ⊢
    constructor
    · linarith [ih.1]
    · linarith [ih.2]
theorem slf_ff_elem (lam : ℝ) (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    fixedFraction lam n (elem n) i =
      if i.val = 0 then 1 - lam else if i.val + 1 = n then lam else 0 := by
  unfold fixedFraction
  rw [slf_sum_elem n (by omega)]
  by_cases h0 : i.val = 0
  · have : ¬ (i.val + 1 = n) := by omega
    have hn1 : ¬ (1 = n) := by omega
    simp [elem, h0, this, hn1]
  · by_cases h1 : i.val + 1 = n
    · simp [elem, h0, h1]
    · simp [elem, h0, h1]

theorem slf_ffinter (lam : ℝ) (n : ℕ) (hn : 2 ≤ n) (i : Fin n) (h1 : 1 ≤ i.val) (h2 : i.val + 1 < n) :
    fixedFraction lam n (elem n) i = 0 := by
  rw [slf_ff_elem lam n hn]
  rw [if_neg (by omega), if_neg (by omega)]
theorem solution (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ) :
    (PopulationMonotone φ ∧ MergingProof φ) ↔
    ∃ lam ∈ Set.Icc (0:ℝ) 1, ∀ n : ℕ, φ n (elem n) = fixedFraction lam n (elem n) := by
  constructor
  · rintro ⟨hpm, hmp⟩
    have hs := slf_ab_sum φ hφ hpm hmp 2 le_rfl
    have n0 := (hφ 2 (elem 2) (slf_isLoss_elem 2)).1.1 0
    have n1 := (hφ 2 (elem 2) (slf_isLoss_elem 2)).1.1 1
    have hs' : φ 2 (elem 2) 0 + φ 2 (elem 2) 1 = 1 := hs
    refine ⟨φ 2 (elem 2) 1, ⟨n1, by linarith⟩, ?_⟩
    intro n
    funext i
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact i.elim0
      · have t := (hφ 1 (elem 1) (slf_isLoss_elem 1)).1.2.2
        rw [slf_sum_elem 1 le_rfl] at t
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at t
        rw [t]
        simp [fixedFraction, elem]
    · rw [slf_ff_elem _ n hn]
      obtain ⟨e0, e1⟩ := slf_endpoints φ hφ hpm hmp n hn
      by_cases h0 : i.val = 0
      · rw [if_pos h0]
        have : i = ⟨0, by omega⟩ := Fin.ext h0
        rw [this, e0]; linarith
      · rw [if_neg h0]
        by_cases h1 : i.val + 1 = n
        · rw [if_pos h1]
          have : i = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [this, e1]
        · rw [if_neg h1]
          exact slf_inter φ hφ hpm hmp n i (by omega) (by omega)
  · rintro ⟨lam, ⟨hl0, hl1⟩, h⟩
    constructor
    · intro n j hj1 hjn i k hi hk
      have hn2 : 2 ≤ n := by omega
      have e1 := h (n + 1)
      have e2 := h n
      have c1 : ∀ x : Fin (n + 1), φ (n + 1) (elem (n + 1)) x =
          if x.val = 0 then 1 - lam else if x.val + 1 = n + 1 then lam else 0 := by
        intro x; rw [e1, slf_ff_elem lam (n + 1) (by omega)]
      have c2 : ∀ x : Fin n, φ n (elem n) x =
          if x.val = 0 then 1 - lam else if x.val + 1 = n then lam else 0 := by
        intro x; rw [e2, slf_ff_elem lam n hn2]
      constructor
      · rw [c1, c2]
        simp only [Fin.val_castSucc]
        by_cases h0 : i.val = 0
        · simp [h0]
        · have hA : ¬ (i.val + 1 = n + 1) := by omega
          have hB : ¬ (i.val + 1 = n) := by omega
          rw [if_neg h0, if_neg h0, if_neg hA, if_neg hB]
      · rw [c1, c2]
        simp only [Fin.val_succ]
        have hk0 : ¬ (k.val = 0) := by omega
        have hk0' : ¬ (k.val + 1 = 0) := by omega
        rw [if_neg hk0', if_neg hk0]
        by_cases hl : k.val + 1 = n
        · rw [if_pos (by omega : k.val + 1 + 1 = n + 1), if_pos hl]
        · rw [if_neg (by omega : ¬ (k.val + 1 + 1 = n + 1)), if_neg hl]
    · have e3 := h 3
      have e2 := h 2
      have c3 : ∀ x : Fin 3, φ 3 (elem 3) x =
          if x.val = 0 then 1 - lam else if x.val + 1 = 3 then lam else 0 := by
        intro x; rw [e3, slf_ff_elem lam 3 (by omega)]
      have c2 : ∀ x : Fin 2, φ 2 (elem 2) x =
          if x.val = 0 then 1 - lam else if x.val + 1 = 2 then lam else 0 := by
        intro x; rw [e2, slf_ff_elem lam 2 le_rfl]
      constructor
      · rw [c3, c3, c2]; simp
      · rw [c3, c3, c2]; simp
