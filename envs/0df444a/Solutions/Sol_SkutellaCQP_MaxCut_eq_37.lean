-- Prove2me | solution 1 for SkutellaCQP.MaxCut.eq_37
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:40:51.990984+00:00
-- url     : https://prove2.me/submissions/fd3d30b4-4699-4527-955e-44b4653cadd3

import Mathlib
import Definitions.Def_SkutellaCQP_MaxCut_Setting

set_option autoImplicit false
open SkutellaCQP.MaxCut

theorem sk_prec_asymm {n : ℕ} (p w : Fin n → ℝ) (j k : Fin n) (h : prec p w j k) :
    ¬ prec p w k j := by
  unfold prec at *
  rintro (h' | ⟨h1', h2'⟩)
  · rcases h with h | ⟨h1, h2⟩
    · linarith
    · linarith
  · rcases h with h | ⟨h1, h2⟩
    · linarith
    · exact absurd h2 (not_lt.mpr h2'.le)

theorem sk_prec_total {n : ℕ} (p w : Fin n → ℝ) (j k : Fin n) (hjk : j ≠ k) :
    prec p w j k ∨ prec p w k j := by
  unfold prec
  rcases lt_trichotomy (w j * p k) (w k * p j) with h | h | h
  · right; left; linarith
  · rcases lt_or_gt_of_ne hjk with h2 | h2
    · left; right; exact ⟨h, h2⟩
    · right; right; exact ⟨h.symm, h2⟩
  · left; left; linarith

theorem sk_edgeW_self {n : ℕ} (p w : Fin n → ℝ) (j : Fin n) : edgeW p w j j = 0 := by
  unfold edgeW prec
  simp

theorem sk_val_eq {m n : ℕ} (p w : Fin n → ℝ) (σ : Fin n → Fin m) :
    val p w σ = ∑ j, w j * p j + ∑ j, ∑ k, (if σ j = σ k then edgeW p w j k else 0) := by
  unfold SkutellaCQP.MaxCut.val SkutellaCQP.MaxCut.compl
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold edgeW
  have h3 : σ j = σ k ↔ σ k = σ j := eq_comm
  by_cases h1 : prec p w k j <;> by_cases h2 : σ k = σ j <;> simp [h1, h2, h3]

theorem sk_cut_add_same {m n : ℕ} (p w : Fin n → ℝ) (σ : Fin n → Fin m) :
    cut p w σ + ∑ j, ∑ k, (if σ j = σ k then edgeW p w j k else 0) = cE p w := by
  unfold cut cE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : σ j = σ k <;> simp [h]

theorem sk_ZCQP_abar {m n : ℕ} (p w : Fin n → ℝ) (hm : 0 < m) :
    ZCQP p w (abar m n) = (1 / 2 + 1 / (2 * (m : ℝ))) * ∑ j, w j * p j + 1 / (m : ℝ) * cE p w := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hcE : cE p w = ∑ j, w j * ∑ k ∈ Finset.univ.filter (fun k => prec p w k j), p k := by
    unfold cE edgeW
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum, Finset.sum_filter]
  unfold ZCQP
  simp only [abar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hcE, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.mul_sum]
  field_simp
  try ring

theorem sk_pair {J : Type*} [DecidableEq J] (R : J → J → Prop) [DecidableRel R]
    (hasymm : ∀ j k, R j k → ¬ R k j) (htot : ∀ j k, j ≠ k → R j k ∨ R k j)
    (y : J → ℝ) (s : Finset J) :
    ∑ j ∈ s, (y j ^ 2 / 2 + ∑ k ∈ s, (if R k j then y j * y k else 0)) =
      (∑ j ∈ s, y j) ^ 2 / 2 := by
  have key : ∀ j k, y j * y k = (if j = k then y j * y k else 0) +
      (if R k j then y j * y k else 0) + (if R j k then y j * y k else 0) := by
    intro j k
    by_cases h : j = k
    · subst h
      have : ¬ R j j := fun h' => hasymm j j h' h'
      simp [this]
    · rcases htot j k h with h1 | h1
      · have := hasymm j k h1
        simp [h, h1, this]
      · have := hasymm k j h1
        simp [h, h1, this]
  have e1 : (∑ j ∈ s, y j) ^ 2 = ∑ j ∈ s, ∑ k ∈ s, y j * y k := by rw [sq, Finset.sum_mul_sum]
  have e2 : ∑ j ∈ s, ∑ k ∈ s, y j * y k =
      ∑ j ∈ s, ∑ k ∈ s, (if j = k then y j * y k else 0) +
      ∑ j ∈ s, ∑ k ∈ s, (if R k j then y j * y k else 0) +
      ∑ j ∈ s, ∑ k ∈ s, (if R j k then y j * y k else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => key j k)
  have e3 : ∑ j ∈ s, ∑ k ∈ s, (if R j k then y j * y k else 0) =
      ∑ j ∈ s, ∑ k ∈ s, (if R k j then y j * y k else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    by_cases h : R k j <;> simp [h, mul_comm]
  have e4 : ∑ j ∈ s, ∑ k ∈ s, (if j = k then y j * y k else 0) = ∑ j ∈ s, y j ^ 2 := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.sum_ite_eq s j]
    simp [hj, sq]
  have e5 : ∑ j ∈ s, (y j ^ 2 / 2 + ∑ k ∈ s, (if R k j then y j * y k else 0)) =
      (∑ j ∈ s, y j ^ 2) / 2 + ∑ j ∈ s, ∑ k ∈ s, (if R k j then y j * y k else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_div]
  rw [e5, e1, e2, e3, e4]
  ring

theorem sk_psd {J : Type*} [DecidableEq J] (R : J → J → Prop) [DecidableRel R]
    (hasymm : ∀ j k, R j k → ¬ R k j) (htot : ∀ j k, j ≠ k → R j k ∨ R k j) (y : J → ℝ) :
    ∀ (s : Finset J) (r : J → ℝ), (∀ j ∈ s, 0 ≤ r j) → (∀ j ∈ s, ∀ k ∈ s, R k j → r j ≤ r k) →
      0 ≤ ∑ j ∈ s, r j * (y j ^ 2 / 2 + ∑ k ∈ s, (if R k j then y j * y k else 0)) := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro r hr hmono
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image s r hne
    have hm00 : 0 ≤ r j0 := hr j0 hj0
    have hdec : ∑ j ∈ s, r j * (y j ^ 2 / 2 + ∑ k ∈ s, (if R k j then y j * y k else 0)) =
        r j0 * ((∑ j ∈ s, y j) ^ 2 / 2) +
        ∑ j ∈ s.erase j0, (r j - r j0) *
          (y j ^ 2 / 2 + ∑ k ∈ s.erase j0, (if R k j then y j * y k else 0)) := by
      rw [← sk_pair R hasymm htot y s, Finset.mul_sum]
      have h1 : ∀ j ∈ s, r j * (y j ^ 2 / 2 + ∑ k ∈ s, (if R k j then y j * y k else 0)) =
          r j0 * (y j ^ 2 / 2 + ∑ k ∈ s, (if R k j then y j * y k else 0)) +
          (r j - r j0) * (y j ^ 2 / 2 + ∑ k ∈ s, (if R k j then y j * y k else 0)) := by
        intro j _; ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      congr 1
      have hs1 := Finset.add_sum_erase s (fun j => (r j - r j0) *
        (y j ^ 2 / 2 + ∑ k ∈ s, (if R k j then y j * y k else 0))) hj0
      rw [← hs1]
      have h0 : (r j0 - r j0) * (y j0 ^ 2 / 2 + ∑ k ∈ s, (if R k j0 then y j0 * y k else 0)) = 0 := by
        ring
      simp only [h0, zero_add]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjs : j ∈ s := Finset.mem_of_mem_erase hj
      have hsplit := Finset.add_sum_erase s (fun k => if R k j then y j * y k else 0) hj0
      rw [← hsplit]
      by_cases hR : R j0 j
      · have : r j - r j0 = 0 := by
          have h1 := hmono j hjs j0 hj0 hR
          have h2 := hmin j hjs
          linarith
        rw [this]; ring
      · simp [hR]
    rw [hdec]
    have h2 := ih (s.erase j0) (Finset.erase_ssubset hj0) (fun j => r j - r j0)
      (fun j hj => sub_nonneg.mpr (hmin j (Finset.mem_of_mem_erase hj)))
      (fun j hj k hk hRkj => by
        have := hmono j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk) hRkj
        show r j - r j0 ≤ r k - r j0
        linarith)
    have h2' : 0 ≤ ∑ j ∈ s.erase j0, (r j - r j0) *
        (y j ^ 2 / 2 + ∑ k ∈ s.erase j0, (if R k j then y j * y k else 0)) := h2
    exact add_nonneg (mul_nonneg hm00 (by positivity)) h2'

theorem sk_inner {m n : ℕ} (σ : Fin n → Fin m) (hm : 0 < m) (j k : Fin n) :
    ∑ i : Fin m, ((if σ j = i then (1 : ℝ) else 0) - 1 / (m : ℝ)) *
        ((if σ k = i then (1 : ℝ) else 0) - 1 / (m : ℝ))
      = (if σ j = σ k then (1 : ℝ) else 0) - 1 / (m : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have h1 : ∑ i : Fin m, (if σ j = i then (1 : ℝ) else 0) = 1 := by simp
  have h2 : ∑ i : Fin m, (if σ k = i then (1 : ℝ) else 0) = 1 := by simp
  have h3 : ∑ i : Fin m, (if σ j = i then (1 : ℝ) else 0) * (if σ k = i then (1 : ℝ) else 0) =
      if σ j = σ k then 1 else 0 := by
    by_cases h : σ j = σ k
    · rw [if_pos h]; simp [h]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : σ j = i
      · have : σ k ≠ i := fun h' => h (hi.trans h'.symm)
        simp [hi, this]
      · simp [hi]
  have : ∀ i : Fin m, ((if σ j = i then (1 : ℝ) else 0) - 1 / (m : ℝ)) *
        ((if σ k = i then (1 : ℝ) else 0) - 1 / (m : ℝ)) =
      (if σ j = i then (1 : ℝ) else 0) * (if σ k = i then (1 : ℝ) else 0)
        - 1 / (m : ℝ) * (if σ j = i then (1 : ℝ) else 0)
        - 1 / (m : ℝ) * (if σ k = i then (1 : ℝ) else 0) + 1 / (m : ℝ) * (1 / (m : ℝ)) := by
    intro i; ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, h1, h2, h3, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

theorem sk_core {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hm : 0 < m) (σ : Fin n → Fin m) :
    1 / (m : ℝ) * cE p w - (1 / 2 - 1 / (2 * (m : ℝ))) * ∑ j, w j * p j ≤
      ∑ j, ∑ k, (if σ j = σ k then edgeW p w j k else 0) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  obtain ⟨y, hy⟩ : ∃ y : Fin m → Fin n → ℝ,
      ∀ i j, y i j = p j * ((if σ j = i then (1 : ℝ) else 0) - 1 / (m : ℝ)) := ⟨_, fun _ _ => rfl⟩
  have hQ : ∀ i : Fin m, 0 ≤ ∑ j, (w j / p j) *
      (y i j ^ 2 / 2 + ∑ k, (if prec p w k j then y i j * y i k else 0)) := by
    intro i
    refine sk_psd (prec p w) (sk_prec_asymm p w) (sk_prec_total p w) (y i) Finset.univ
      (fun j => w j / p j) (fun j _ => div_nonneg (hw j) (hp j).le) (fun j _ k _ hR => ?_)
    show w j / p j ≤ w k / p k
    rw [div_le_div_iff₀ (hp j) (hp k)]
    rcases hR with h | ⟨h, _⟩ <;> linarith
  have hsum := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hQ i)
  have S1 : ∀ j, ∑ i, y i j ^ 2 = p j ^ 2 * (1 - 1 / (m : ℝ)) := by
    intro j
    have := sk_inner σ hm j j
    simp only [if_true] at this
    calc ∑ i, y i j ^ 2 = ∑ i, p j ^ 2 * (((if σ j = i then (1 : ℝ) else 0) - 1 / (m : ℝ)) *
          ((if σ j = i then (1 : ℝ) else 0) - 1 / (m : ℝ))) := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [hy]; ring
      _ = p j ^ 2 * (1 - 1 / (m : ℝ)) := by rw [← Finset.mul_sum, this]
  have S2 : ∀ j k, ∑ i, y i j * y i k =
      p j * p k * ((if σ j = σ k then (1 : ℝ) else 0) - 1 / (m : ℝ)) := by
    intro j k
    rw [← sk_inner σ hm j k, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hy, hy]; ring
  have hj : ∀ j, ∑ i : Fin m, (w j / p j) *
      (y i j ^ 2 / 2 + ∑ k, (if prec p w k j then y i j * y i k else 0)) =
      (1 / 2 - 1 / (2 * (m : ℝ))) * (w j * p j) +
        ∑ k, (if σ j = σ k then edgeW p w j k else 0) - 1 / (m : ℝ) * ∑ k, edgeW p w j k := by
    intro j
    have hpj := (hp j).ne'
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm (f := fun i k =>
      if prec p w k j then y i j * y i k else 0)]
    have e1 : ∑ i, y i j ^ 2 / 2 = p j ^ 2 * (1 - 1 / (m : ℝ)) / 2 := by
      rw [← Finset.sum_div, S1]
    have e2 : ∀ k, ∑ i, (if prec p w k j then y i j * y i k else 0) =
        if prec p w k j then p j * p k * ((if σ j = σ k then (1 : ℝ) else 0) - 1 / (m : ℝ)) else 0 := by
      intro k
      by_cases h : prec p w k j
      · simp only [if_pos h]; rw [← S2 j k]
      · simp [h]
    rw [e1, Finset.sum_congr rfl (fun k _ => e2 k), mul_add, Finset.mul_sum]
    have e3 : ∀ k, w j / p j * (if prec p w k j then p j * p k *
        ((if σ j = σ k then (1 : ℝ) else 0) - 1 / (m : ℝ)) else 0) =
        (if σ j = σ k then edgeW p w j k else 0) - 1 / (m : ℝ) * edgeW p w j k := by
      intro k
      unfold edgeW
      by_cases h : prec p w k j <;> by_cases h' : σ j = σ k <;> simp [h, h'] <;> field_simp
    rw [Finset.sum_congr rfl (fun k _ => e3 k), Finset.sum_sub_distrib, ← Finset.mul_sum]
    field_simp
    ring
  rw [Finset.sum_comm] at hsum
  rw [Finset.sum_congr rfl (fun j _ => hj j)] at hsum
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hcE : cE p w = ∑ j, ∑ k, edgeW p w j k := rfl
  rw [hcE]
  linarith

theorem solution {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j) (hm : 0 < m) :
    ZCQP p w (abar m n) =
        1 / (m : ℝ) * cE p w + (1 / 2 + 1 / (2 * (m : ℝ))) * ∑ j, w j * p j ∧
    ∀ τ : Fin n → Fin m, ZCQP p w (abar m n) ≤ val p w τ := by
  have h1 := sk_ZCQP_abar p w hm
  refine ⟨by rw [h1]; ring, fun τ => ?_⟩
  have := sk_core p w hp hw hm τ
  rw [h1, sk_val_eq]
  linarith
