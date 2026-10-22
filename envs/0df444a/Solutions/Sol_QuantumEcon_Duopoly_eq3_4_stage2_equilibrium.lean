-- Prove2me | solution 1 for QuantumEcon.Duopoly.eq3_4_stage2_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:42:31.413616+00:00
-- url     : https://prove2.me/submissions/1e789816-765f-49d7-b6d3-44f071f8e04f

import Mathlib
import Definitions.Def_QuantumEcon_Duopoly_Setting
set_option autoImplicit false
open QuantumEcon.Duopoly

theorem gg_br (r q : ℝ) (hq : 0 ≤ q) (h : ∀ x : ℝ, 0 ≤ x → (r - x) * x ≤ (r - q) * q) :
    q = max 0 (r / 2) := by
  by_cases hr : r ≤ 0
  · have h0 := h 0 le_rfl
    have : q = 0 := by
      by_contra hne
      have hpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
      nlinarith [mul_pos hpos hpos]
    rw [this]; simp; linarith
  · push_neg at hr
    have h1 := h (r / 2) (by linarith)
    have : q = r / 2 := by
      have : (q - r / 2) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg _))
      linarith
    rw [this]; simp; linarith

theorem gg_br' (r q : ℝ) (hqe : q = max 0 (r / 2)) :
    ∀ x : ℝ, 0 ≤ x → (r - x) * x ≤ (r - q) * q := by
  intro x hx
  by_cases hr : r ≤ 0
  · have : q = 0 := by rw [hqe]; simp; linarith
    rw [this]; nlinarith
  · push_neg at hr
    have : q = r / 2 := by rw [hqe]; simp; linarith
    rw [this]; nlinarith [sq_nonneg (x - r / 2)]

theorem solution (P : Params) (hP : Standing P)
    (x₁ x₂ q₁ q₂ : ℝ) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hq₁ : 0 ≤ qStar₁ P x₁ x₂) (hq₂ : 0 ≤ qStar₂ P x₁ x₂) :
    IsStage2Nash P x₁ x₂ q₁ q₂ ↔
      q₁ = qStar₁ P x₁ x₂ ∧ q₂ = qStar₂ P x₁ x₂ := by
  obtain ⟨hg0, hg1, hc1, hcc, hca, hB1, hB2⟩ := hP
  have hD : P.γ ^ 2 - 4 ≠ 0 := by nlinarith
  have hD' : -4 + P.γ ^ 2 ≠ 0 := by intro h; apply hD; linarith
  have e1 : 2 * qStar₁ P x₁ x₂ = (P.a + x₁ - P.c - P.γ * qStar₂ P x₁ x₂) := by
    unfold qStar₁ qStar₂; field_simp; ring
  have e2 : 2 * qStar₂ P x₁ x₂ = (P.a + x₂ - P.c ^ 2 - P.γ * qStar₁ P x₁ x₂) := by
    unfold qStar₁ qStar₂; field_simp; ring
  have s1 : qStar₁ P x₁ x₂ = max 0 ((P.a + x₁ - P.c - P.γ * qStar₂ P x₁ x₂) / 2) := by
    rw [← e1]; simp [hq₁]
  have s2 : qStar₂ P x₁ x₂ = max 0 ((P.a + x₂ - P.c ^ 2 - P.γ * qStar₁ P x₁ x₂) / 2) := by
    rw [← e2]; simp [hq₂]
  unfold IsStage2Nash SupplierAudit.Competition.IsCournotNash SupplierAudit.Competition.cournotPayoff
  constructor
  · rintro ⟨h1, h2, hb1, hb2⟩
    have n1 : q₁ = max 0 ((P.a + x₁ - P.c - P.γ * q₂) / 2) := by
      apply gg_br _ _ h1
      intro x hx
      have := hb1 x hx
      nlinarith
    have n2 : q₂ = max 0 ((P.a + x₂ - P.c ^ 2 - P.γ * q₁) / 2) := by
      apply gg_br _ _ h2
      intro x hx
      have := hb2 x hx
      nlinarith
    set d1 := q₁ - qStar₁ P x₁ x₂ with hd1
    set d2 := q₂ - qStar₂ P x₁ x₂ with hd2
    have b1 : |d1| ≤ |d2| / 2 := by
      have := abs_max_sub_max_le_abs ((P.a + x₁ - P.c - P.γ * q₂) / 2)
        ((P.a + x₁ - P.c - P.γ * qStar₂ P x₁ x₂) / 2) 0
      rw [max_comm _ 0, max_comm _ 0, ← n1, ← s1] at this
      have e : (P.a + x₁ - P.c - P.γ * q₂) / 2 - (P.a + x₁ - P.c - P.γ * qStar₂ P x₁ x₂) / 2
          = -(P.γ * d2) / 2 := by rw [hd2]; ring
      rw [e, abs_div, abs_neg, abs_mul, abs_of_nonneg hg0] at this
      have h22 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
      rw [h22] at this
      have : P.γ * |d2| ≤ |d2| := by nlinarith [abs_nonneg d2]
      calc |d1| ≤ P.γ * |d2| / 2 := by assumption
        _ ≤ |d2| / 2 := by linarith
    have b2 : |d2| ≤ |d1| / 2 := by
      have := abs_max_sub_max_le_abs ((P.a + x₂ - P.c ^ 2 - P.γ * q₁) / 2)
        ((P.a + x₂ - P.c ^ 2 - P.γ * qStar₁ P x₁ x₂) / 2) 0
      rw [max_comm _ 0, max_comm _ 0, ← n2, ← s2] at this
      have e : (P.a + x₂ - P.c ^ 2 - P.γ * q₁) / 2 - (P.a + x₂ - P.c ^ 2 - P.γ * qStar₁ P x₁ x₂) / 2
          = -(P.γ * d1) / 2 := by rw [hd1]; ring
      rw [e, abs_div, abs_neg, abs_mul, abs_of_nonneg hg0] at this
      have h22 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
      rw [h22] at this
      have : P.γ * |d1| ≤ |d1| := by nlinarith [abs_nonneg d1]
      calc |d2| ≤ P.γ * |d1| / 2 := by assumption
        _ ≤ |d1| / 2 := by linarith
    have z1 : |d1| = 0 := by nlinarith [abs_nonneg d1, abs_nonneg d2]
    have z2 : |d2| = 0 := by nlinarith [abs_nonneg d1, abs_nonneg d2]
    constructor
    · have := abs_eq_zero.mp z1; linarith
    · have := abs_eq_zero.mp z2; linarith
  · rintro ⟨rfl, rfl⟩
    refine ⟨hq₁, hq₂, ?_, ?_⟩
    · intro x hx
      have := gg_br' _ _ s1 x hx
      nlinarith
    · intro x hx
      have := gg_br' _ _ s2 x hx
      nlinarith
