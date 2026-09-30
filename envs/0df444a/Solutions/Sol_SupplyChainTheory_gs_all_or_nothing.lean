-- Prove2me | solution 1 for SupplyChainTheory.gs_all_or_nothing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T06:24:54.368136+00:00
-- url     : https://prove2.me/submissions/5e905c87-77e4-411e-b5ed-483b90a83864

import Mathlib
import Definitions.Def_SupplyChainTheory_multiechelon

set_option autoImplicit false

namespace SupplyChainTheory

lemma gsaon_chain (f : ℕ → ℝ) (m k : ℕ)
    (h : ∀ j, m ≤ j → j < m + k → f (j + 1) ≤ f j) : f (m + k) ≤ f m := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    have h1 : f (m + 1 + k) ≤ f (m + 1) := ih (m + 1) (fun j hj1 hj2 => h j (by omega) (by omega))
    have h2 : f (m + 1) ≤ f m := h m le_rfl (by omega)
    have e : m + (k + 1) = m + 1 + k := by omega
    rw [e]; linarith

lemma gsaon_sqrt_le (u v w : ℝ) (hw : v + w = 0) (h1 : 0 ≤ u + v) (h2 : 0 ≤ u + w) :
    Real.sqrt (u + v) + Real.sqrt (u + w) ≤ 2 * Real.sqrt u := by
  have hu : 0 ≤ u := by linarith
  have hp := Real.sq_sqrt h1
  have hq := Real.sq_sqrt h2
  have hs := Real.sq_sqrt hu
  have p0 := Real.sqrt_nonneg (u + v)
  have q0 := Real.sqrt_nonneg (u + w)
  have s0 := Real.sqrt_nonneg u
  nlinarith [sq_nonneg (Real.sqrt (u + v) - Real.sqrt (u + w)),
    sq_nonneg (Real.sqrt (u + v) + Real.sqrt (u + w) - 2 * Real.sqrt u)]

lemma gsaon_sqrt_lt (u v w : ℝ) (hw : v + w = 0) (hv : v ≠ 0) (h1 : 0 ≤ u + v) (h2 : 0 ≤ u + w) :
    Real.sqrt (u + v) + Real.sqrt (u + w) < 2 * Real.sqrt u := by
  have hu : 0 ≤ u := by linarith
  have hp := Real.sq_sqrt h1
  have hq := Real.sq_sqrt h2
  have hs := Real.sq_sqrt hu
  have p0 := Real.sqrt_nonneg (u + v)
  have q0 := Real.sqrt_nonneg (u + w)
  have s0 := Real.sqrt_nonneg u
  have hne : Real.sqrt (u + v) - Real.sqrt (u + w) ≠ 0 := by
    intro h0
    have : Real.sqrt (u + v) = Real.sqrt (u + w) := by linarith
    have : u + v = u + w := by rw [← hp, ← hq, this]
    apply hv; linarith
  have hpos : 0 < (Real.sqrt (u + v) - Real.sqrt (u + w)) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  nlinarith [sq_nonneg (Real.sqrt (u + v) + Real.sqrt (u + w) - 2 * Real.sqrt u)]

end SupplyChainTheory

open SupplyChainTheory in
theorem solution (N : ℕ) (h : ℕ → ℝ) (k : ℝ) (T : ℕ → ℝ) (SIN : ℝ)
    (hk : 0 < k) (hh : ∀ i ∈ Finset.Icc 1 N, 0 < h i) (hT : ∀ i, 0 ≤ T i) (hSI : 0 ≤ SIN)
    (S : ℕ → ℝ) (hS1 : S 1 = 0) (hfeas : GSFeasible N T SIN S)
    (hopt : ∀ S' : ℕ → ℝ, S' 1 = 0 → GSFeasible N T SIN S' →
      gsCost N h k T SIN S ≤ gsCost N h k T SIN S') :
    ∀ i ∈ Finset.Icc 2 N, S i = 0 ∨ S i = gsInbound N SIN S i + T i := by
  classical
  intro i hi
  obtain ⟨hi2, hiN⟩ := Finset.mem_Icc.mp hi
  by_contra hcon
  push_neg at hcon
  obtain ⟨hS0, hSx⟩ := hcon
  obtain ⟨hnn, hlt⟩ := hfeas
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℝ, X = fun j => gsInbound N SIN S j + T j - S j := ⟨_, rfl⟩
  have hXnn : ∀ j ∈ Finset.Icc 1 N, 0 ≤ X j := fun j hj => by
    rw [hX]; linarith [hlt j hj]
  have hiI : i ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hiN⟩
  have hSi : 0 < S i := lt_of_le_of_ne (hnn i hiI) (Ne.symm hS0)
  have hXi : 0 < X i := lt_of_le_of_ne (hXnn i hiI) (by
    intro h0; apply hSx; rw [hX] at h0; simp only at h0; linarith)
  have chain : ∀ m, m ≤ i → (∀ j, m ≤ j → j < i → X j = 0) → S i ≤ S m := by
    intro m hm hz
    have := gsaon_chain S m (i - m) (fun j hj1 hj2 => by
      have hx := hz j hj1 (by omega)
      have hjN : j < N := by omega
      rw [hX] at hx
      simp only [gsInbound, if_pos hjN] at hx
      linarith [hT j])
    rwa [Nat.add_sub_cancel' hm] at this
  have hex : ∃ j, j ≤ i - 1 ∧ (1 ≤ j ∧ j < i ∧ 0 < X j) := by
    by_contra hne
    push_neg at hne
    have := chain 1 (by omega) (fun j hj1 hj2 =>
      le_antisymm (hne j (by omega) hj1 hj2) (hXnn j (Finset.mem_Icc.mpr ⟨hj1, by omega⟩)))
    linarith
  obtain ⟨j0, hj0, hPj0⟩ := hex
  obtain ⟨b, hb⟩ : ∃ b, b = Nat.findGreatest (fun j => 1 ≤ j ∧ j < i ∧ 0 < X j) (i - 1) :=
    ⟨_, rfl⟩
  have hPb : 1 ≤ b ∧ b < i ∧ 0 < X b := by
    rw [hb]; exact Nat.findGreatest_spec (P := fun j => 1 ≤ j ∧ j < i ∧ 0 < X j) hj0 hPj0
  have hzero : ∀ j, b < j → j < i → X j = 0 := by
    intro j h1 h2
    have hng := Nat.findGreatest_is_greatest (P := fun j => 1 ≤ j ∧ j < i ∧ 0 < X j)
      (n := i - 1) (k := j) (by rw [← hb]; exact h1) (by omega)
    have hnn' := hXnn j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    simp only [not_and, not_lt] at hng
    exact le_antisymm (hng (by omega) h2) hnn'
  have hSj : ∀ j, b < j → j ≤ i → S i ≤ S j := fun j h1 h2 =>
    chain j h2 (fun l hl1 hl2 => hzero l (by omega) hl2)
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℝ, d = fun j => if b < j ∧ j ≤ i then 1 else 0 := ⟨_, rfl⟩
  have hcb : d (b + 1) - d b = 1 := by
    rw [hd]; simp only
    rw [if_pos (by omega), if_neg (by omega)]; norm_num
  have hci : d (i + 1) - d i = -1 := by
    rw [hd]; simp only
    rw [if_neg (by omega), if_pos (by omega)]; norm_num
  have hc0 : ∀ j, j ≠ b → j ≠ i → d (j + 1) - d j = 0 := by
    intro j h1 h2
    have e1 : (b < j + 1 ∧ j + 1 ≤ i) ↔ (b < j ∧ j ≤ i) := by
      constructor <;> rintro ⟨h3, h4⟩ <;> constructor <;> omega
    rw [hd]; simp only [e1, sub_self]
  have hXS' : ∀ t : ℝ, ∀ j ∈ Finset.Icc 1 N,
      gsInbound N SIN (fun l => S l + t * d l) j + T j - (S j + t * d j)
        = X j + t * (d (j + 1) - d j) := by
    intro t j hj
    have hj' := Finset.mem_Icc.mp hj
    rw [hX]
    simp only [gsInbound]
    by_cases hjN : j < N
    · simp only [if_pos hjN]; ring
    · simp only [if_neg hjN]
      have : d (j + 1) = 0 := by
        rw [hd]; simp only; rw [if_neg (by omega)]
      rw [this]; ring
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (X b) (min (X i) (S i)) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hε]; exact lt_min hPb.2.2 (lt_min hXi hSi)
  have hεb : ε ≤ X b := by rw [hε]; exact min_le_left _ _
  have hεi : ε ≤ X i := by rw [hε]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεS : ε ≤ S i := by rw [hε]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hnonneg : ∀ t : ℝ, -ε ≤ t → t ≤ ε → ∀ j ∈ Finset.Icc 1 N,
      0 ≤ X j + t * (d (j + 1) - d j) := by
    intro t ht1 ht2 j hj
    by_cases hjb : j = b
    · subst hjb; rw [hcb]; linarith
    by_cases hji : j = i
    · subst hji; rw [hci]; linarith
    rw [hc0 j hjb hji]; linarith [hXnn j hj]
  have hfeasT : ∀ t : ℝ, -ε ≤ t → t ≤ ε →
      (fun l => S l + t * d l) 1 = 0 ∧ GSFeasible N T SIN (fun l => S l + t * d l) := by
    intro t ht1 ht2
    refine ⟨?_, ?_, ?_⟩
    · have : d 1 = 0 := by rw [hd]; simp only; rw [if_neg (by omega)]
      simp only [this, hS1]; ring
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      by_cases hc : b < j ∧ j ≤ i
      · have : d j = 1 := by rw [hd]; simp only; rw [if_pos hc]
        simp only [this]
        have := hSj j hc.1 hc.2
        linarith
      · have : d j = 0 := by rw [hd]; simp only; rw [if_neg hc]
        simp only [this]
        linarith [hnn j hj]
    · intro j hj
      have := hXS' t j hj
      have := hnonneg t ht1 ht2 j hj
      simp only
      linarith
  have hcost : ∀ t : ℝ, gsCost N h k T SIN (fun l => S l + t * d l)
      = ∑ j ∈ Finset.Icc 1 N, h j * k * Real.sqrt (X j + t * (d (j + 1) - d j)) := by
    intro t
    simp only [gsCost]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← hXS' t j hj]
  have hcost0 : gsCost N h k T SIN S = ∑ j ∈ Finset.Icc 1 N, h j * k * Real.sqrt (X j) := by
    rw [hX]; rfl
  have c1 := hopt _ (hfeasT ε (by linarith) le_rfl).1 (hfeasT ε (by linarith) le_rfl).2
  have c2 := hopt _ (hfeasT (-ε) le_rfl (by linarith)).1 (hfeasT (-ε) le_rfl (by linarith)).2
  rw [hcost, hcost0] at c1 c2
  have key : ∑ j ∈ Finset.Icc 1 N, h j * k * Real.sqrt (X j + ε * (d (j + 1) - d j))
      + ∑ j ∈ Finset.Icc 1 N, h j * k * Real.sqrt (X j + -ε * (d (j + 1) - d j))
      < 2 * ∑ j ∈ Finset.Icc 1 N, h j * k * Real.sqrt (X j) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro j hj
      have hpos : 0 < h j * k := mul_pos (hh j hj) hk
      have hle := gsaon_sqrt_le (X j) (ε * (d (j + 1) - d j)) (-ε * (d (j + 1) - d j))
        (by ring) (hnonneg ε (by linarith) le_rfl j hj) (hnonneg (-ε) le_rfl (by linarith) j hj)
      nlinarith
    · refine ⟨i, hiI, ?_⟩
      have hpos : 0 < h i * k := mul_pos (hh i hiI) hk
      have hlt' := gsaon_sqrt_lt (X i) (ε * (d (i + 1) - d i)) (-ε * (d (i + 1) - d i))
        (by ring) (by rw [hci]; linarith)
        (hnonneg ε (by linarith) le_rfl i hiI) (hnonneg (-ε) le_rfl (by linarith) i hiI)
      nlinarith
  linarith
