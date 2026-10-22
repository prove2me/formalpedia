-- Prove2me | solution 1 for OpenPitMIP.UltPit.dominated_triplet
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:27:44.532951+00:00
-- url     : https://prove2.me/submissions/a5078af4-512d-42e8-8c0f-ef5de12eba8f

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

set_option autoImplicit false
open OpenPitMIP.UltPit PCPSPC

theorem qqc_dt_key {B D : Type} [Fintype B] [Fintype D] {T : ℕ} [DecidableEq B] [DecidableEq D]
    [DecidableEq (Fin T)] (b : B) (d₁ d₂ : D) (t : Fin T) (a : ℝ) (f : B → D → Fin T → ℝ) :
    ∑ b', ∑ d', ∑ t', f b' d' t' *
      (if b' = b ∧ t' = t then ((if d' = d₁ then a else 0) + (if d' = d₂ then -a else 0)) else 0)
      = (f b d₁ t - f b d₂ t) * a := by
  have : ∀ b' d' t', f b' d' t' *
      (if b' = b ∧ t' = t then ((if d' = d₁ then a else 0) + (if d' = d₂ then -a else 0)) else 0)
      = if b' = b then (if t' = t then (if d' = d₁ then f b' d' t' * a else 0)
          + (if d' = d₂ then f b' d' t' * (-a) else 0) else 0) else 0 := by
    intro b' d' t'
    by_cases h1 : b' = b <;> by_cases h2 : t' = t <;> by_cases h3 : d' = d₁ <;>
      by_cases h4 : d' = d₂ <;> simp [h1, h2, h3, h4, mul_add]
  simp only [this]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq', sub_mul]
  ring

theorem qqc_dt_sum {B D : Type} [Fintype B] [Fintype D] {T : ℕ} [DecidableEq B] [DecidableEq D]
    [DecidableEq (Fin T)] (b : B) (d₁ d₂ : D) (hd : d₁ ≠ d₂) (t : Fin T) (a : ℝ) (b' : B) (t' : Fin T) :
    ∑ d', (if b' = b ∧ t' = t then ((if d' = d₁ then a else 0) + (if d' = d₂ then -a else 0)) else 0)
      = 0 := by
  by_cases h : b' = b ∧ t' = t
  · simp [h, Finset.sum_add_distrib]
  · simp [h]

theorem solution {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (κ : Integrality) (b : B) (d₁ d₂ : D) (hd : d₁ ≠ d₂) (t : Fin T)
    (hG : ∀ i, I.G i b d₁ t ≤ I.G i b d₂ t) (hp : I.value b d₁ t ≥ I.value b d₂ t)
    (hopt : ∃ x y, I.Optimal κ x y) :
    ∃ x y, I.Optimal κ x y ∧ y b d₂ t = 0 := by
  classical
  obtain ⟨x, y, ⟨hx, hle, harc, hG', hy, hint⟩, hmax⟩ := hopt
  set a := y b d₂ t with ha
  let Δ : B → D → Fin T → ℝ := fun b' d' t' =>
    if b' = b ∧ t' = t then ((if d' = d₁ then a else 0) + (if d' = d₂ then -a else 0)) else 0
  have hlin : ∀ f : B → D → Fin T → ℝ,
      ∑ b', ∑ d', ∑ t', f b' d' t' * (y b' d' t' + Δ b' d' t') =
        ∑ b', ∑ d', ∑ t', f b' d' t' * y b' d' t' + (f b d₁ t - f b d₂ t) * a := by
    intro f
    have k := qqc_dt_key b d₁ d₂ t a f
    simp only [mul_add, Finset.sum_add_distrib]
    rw [k]
  have ha0 : 0 ≤ a := hy b d₂ t
  have hfeas : I.Feasible κ x (fun b' d' t' => y b' d' t' + Δ b' d' t') := by
    refine ⟨?_, hle, harc, ?_, ?_, hint⟩
    · intro b' t'
      rw [hx b' t', Finset.sum_add_distrib]
      have := qqc_dt_sum b d₁ d₂ hd t a b' t'
      simp only [Δ] at this ⊢
      rw [this, add_zero]
    · intro i
      have := hlin (fun b' d' t' => I.G i b' d' t')
      rw [this]
      have h1 := hG i
      nlinarith [hG' i, mul_nonneg (sub_nonneg.2 (hG i)) ha0]
    · intro b' d' t'
      simp only [Δ]
      by_cases h : b' = b ∧ t' = t
      · obtain ⟨rfl, rfl⟩ := h
        by_cases h1 : d' = d₁
        · subst h1
          simp [hd]
          linarith [hy b' d' t', ha0]
        · by_cases h2 : d' = d₂
          · subst h2; simp [h1, ha]
          · simp [h1, h2]; exact hy _ _ _
      · simp [h]; exact hy _ _ _
  have hobj : I.objective y ≤ I.objective (fun b' d' t' => y b' d' t' + Δ b' d' t') := by
    unfold PCPSPC.objective
    rw [hlin (fun b' d' t' => I.value b' d' t')]
    nlinarith [mul_nonneg (sub_nonneg.2 hp) ha0]
  refine ⟨x, _, ⟨hfeas, ?_⟩, ?_⟩
  · intro x' y' h
    exact (hmax x' y' h).trans hobj
  · simp [Δ, ha]
    intro h; exact absurd h.symm hd
