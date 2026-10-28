-- Prove2me | solution 1 for YieldCheapTalk.Truthful.ic_high_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:30:44.246778+00:00
-- url     : https://prove2.me/submissions/4f7c306b-05c0-4573-9de1-40f61d42b508

import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting

open MeasureTheory

open YieldCheapTalk.Truthful in
theorem solution (M : Model) (hM : M.Standing) :
    (M.IC5 ↔
      ((M.Qr (M.theta .H) (M.a .H) - M.Qr (M.theta .L) (M.a .H)) * M.mu .H .H ≥
          (M.Qr (M.theta .L) (M.a .L) - M.Qr (M.theta .H) (M.a .L)) * M.mu .L .H ∧
        (M.Qr (M.theta .L) (M.a .H) - M.Qr (M.theta .H) (M.a .H)) * M.mu .H .L ≥
          (M.Qr (M.theta .H) (M.a .L) - M.Qr (M.theta .L) (M.a .L)) * M.mu .L .L)) ∧
    ((M.Qr (M.theta .H) (M.a .H) - M.Qr (M.theta .L) (M.a .H)) * M.mu .H .H ≥
          (M.Qr (M.theta .L) (M.a .L) - M.Qr (M.theta .H) (M.a .L)) * M.mu .L .H ↔
      ∑ m, M.mu m .H * M.a m ≤
        (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w) := by
  have huniv : (Finset.univ : Finset Level) = {Level.H, Level.L} := rfl
  have hHL : Level.H ≠ Level.L := by decide
  constructor
  · constructor
    · intro h
      have h1 := h .H .L hHL
      have h2 := h .L .H hHL.symm
      constructor <;> linarith
    · rintro ⟨h1, h2⟩ t t' hne
      cases t <;> cases t'
      · exact absurd rfl hne
      · linarith
      · linarith
      · exact absurd rfl hne
  · -- positivity of thetas
    have hθL0 : 0 ≤ M.theta .L := by
      rw [← hM.mean .L]
      haveI := hM.isProb .L
      exact integral_nonneg_of_ae ((hM.support .L).mono (fun x hx => hx.1))
    have hη0 : 0 ≤ M.eta := hM.eta_mem.1
    have hθL : 0 < M.theta .L := by
      rcases eq_or_lt_of_le hθL0 with h | h
      · exfalso
        have := hM.buyer_pos .H .L
        rw [← h] at this
        have : 0 ≤ M.eta * M.w := mul_nonneg hη0 hM.w_pos.le
        linarith
      · exact h
    have hθH : 0 < M.theta .H := lt_trans hθL hM.theta_lt
    -- mu sum
    have hsum : M.mu .H .H + M.mu .L .H = 1 := by
      unfold Model.mu
      rw [huniv, Finset.sum_pair hHL, ← add_div]
      have : 0 < M.p .H .H + M.p .H .L := add_pos (hM.p_pos _ _) (hM.p_pos _ _)
      exact div_self this.ne'
    have hS : ∑ m, M.mu m .H * M.a m = M.mu .H .H * M.a .H + M.mu .L .H * M.a .L := by
      rw [huniv, Finset.sum_pair hHL]
    rw [hS]
    set k := 2 * M.b * (1 + M.delta ^ 2) with hk
    have hkpos : 0 < k := by have := hM.b_pos; positivity
    set mH := M.mu .H .H
    set mL := M.mu .L .H
    have hmL : mL = 1 - mH := by linarith
    set c := (1 / M.theta .H - 1 / M.theta .L) / k with hc
    have hcneg : c < 0 := by
      apply div_neg_of_neg_of_pos _ hkpos
      rw [sub_neg]
      exact one_div_lt_one_div_of_lt hθL hM.theta_lt
    have key : (M.Qr (M.theta .H) (M.a .H) - M.Qr (M.theta .L) (M.a .H)) * mH -
        (M.Qr (M.theta .L) (M.a .L) - M.Qr (M.theta .H) (M.a .L)) * mL =
        c * ((mH * M.a .H + mL * M.a .L) -
          (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w) := by
      unfold Model.Qr
      rw [← hk, hc, hmL]
      field_simp
      ring
    constructor
    · intro h
      by_contra hcon
      push_neg at hcon
      have : c * ((mH * M.a .H + mL * M.a .L) -
          (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w) < 0 :=
        mul_neg_of_neg_of_pos hcneg (by linarith)
      linarith
    · intro h
      have : 0 ≤ c * ((mH * M.a .H + mL * M.a .L) -
          (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w) :=
        mul_nonneg_of_nonpos_of_nonpos hcneg.le (by linarith)
      linarith
