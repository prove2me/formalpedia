-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__rows_num_pair_e1a5b5481773
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:41:29.37651+00:00
-- url     : https://prove2.me/submissions/f1e91c25-e6b9-45ee-91b7-fa9a706d8d65

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsNum
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rows_num_l_c160d0e13346
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.MainNotions.BridgeLemma₂
private theorem pow_rpow_eq_rpow_mul {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (z : ℝ) :
    (x ^ n) ^ z = x ^ ((n : ℝ) * z) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
end Formalism.MainNotions.BridgeLemma₂
end

set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {P σ₁ σ₂ h₁ h₂ cr Γ a2 dq E1 F6 XiH XiP ck e l₁ l₂ : ℝ} (hP : 1 ≤ P) (hσ₁ : 1 ≤ σ₁) (hσ₂ : 1 ≤ σ₂)
    (h1₁ : 1 ≤ h₁) (h1₂ : 1 ≤ h₂) (hh₁ : h₁ ≤ P * σ₁ ^ 4) (hh₂ : h₂ ≤ P * σ₂ ^ 4) (hcr : 0 ≤ cr) (hΓ : 0 ≤ Γ)
    (hE1 : 0 ≤ E1) (hF6 : 0 ≤ F6) (hXiH : 0 ≤ XiH) (hXi : XiH ≤ XiP * (σ₁ * σ₂) ^ (4 * ck))
    (hl₁ : l₁ = (h₁ ^ cr) ^ 2 * (Γ * σ₁ ^ a2) * σ₁ ^ (-dq)) (hl₂ : l₂ = (h₂ ^ cr) ^ 2 * (Γ * σ₂ ^ a2) * σ₂ ^ (-dq))
    (he : 4 * ck + 4 * E1 + 4 * cr + a2 / 2 - dq / 2 ≤ -e) :
    XiH * ((h₁ * h₂) ^ E1 * F6) * Real.sqrt (l₁ * l₂) ≤
      XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) * (σ₁ ^ (-e) * σ₂ ^ (-e)) := by
  have hP0 : 0 < P := by linarith
  have hσ₁0 : 0 < σ₁ := by linarith
  have hσ₂0 : 0 < σ₂ := by linarith
  have hS1 : 1 ≤ σ₁ * σ₂ := by nlinarith
  have hS0 : 0 < σ₁ * σ₂ := by linarith
  have hA : 0 ≤ (P ^ cr) ^ 2 * Γ := mul_nonneg (sq_nonneg _) hΓ
  have hb₁ : l₁ ≤ (P ^ cr) ^ 2 * Γ * σ₁ ^ (8 * cr + a2 - dq) := by
    rw [hl₁]; exact rows_num_l hP hσ₁ h1₁ hh₁ hcr hΓ
  have hb₂ : l₂ ≤ (P ^ cr) ^ 2 * Γ * σ₂ ^ (8 * cr + a2 - dq) := by
    rw [hl₂]; exact rows_num_l hP hσ₂ h1₂ hh₂ hcr hΓ
  have hl₂0 : 0 ≤ l₂ := by
    rw [hl₂]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hΓ (Real.rpow_nonneg hσ₂0.le _)))
      (Real.rpow_nonneg hσ₂0.le _)
  have hhalf : (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2) * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)
      = σ₁ ^ (8 * cr + a2 - dq) * σ₂ ^ (8 * cr + a2 - dq) := by
    rw [← Real.rpow_add hS0, ← Real.mul_rpow hσ₁0.le hσ₂0.le]
    congr 1
    ring
  have hsq : Real.sqrt (l₁ * l₂) ≤ (P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2) := by
    have hprod : l₁ * l₂ ≤ ((P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) ^ 2 := by
      calc l₁ * l₂ ≤ ((P ^ cr) ^ 2 * Γ * σ₁ ^ (8 * cr + a2 - dq)) *
            ((P ^ cr) ^ 2 * Γ * σ₂ ^ (8 * cr + a2 - dq)) :=
            mul_le_mul hb₁ hb₂ hl₂0 (mul_nonneg hA (Real.rpow_nonneg hσ₁0.le _))
        _ = ((P ^ cr) ^ 2 * Γ) ^ 2 * (σ₁ ^ (8 * cr + a2 - dq) * σ₂ ^ (8 * cr + a2 - dq)) := by ring
        _ = ((P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) ^ 2 := by rw [← hhalf]; ring
    calc Real.sqrt (l₁ * l₂)
        ≤ Real.sqrt (((P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) ^ 2) :=
          Real.sqrt_le_sqrt hprod
      _ = (P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2) :=
          Real.sqrt_sq (mul_nonneg hA (Real.rpow_nonneg hS0.le _))
  have hE : (h₁ * h₂) ^ E1 ≤ (P ^ E1) ^ 2 * (σ₁ * σ₂) ^ (4 * E1) := by
    have hprod : h₁ * h₂ ≤ P ^ 2 * (σ₁ * σ₂) ^ 4 := by
      calc h₁ * h₂ ≤ (P * σ₁ ^ 4) * (P * σ₂ ^ 4) :=
            mul_le_mul hh₁ hh₂ (by linarith) (mul_nonneg hP0.le (pow_nonneg hσ₁0.le 4))
        _ = P ^ 2 * (σ₁ * σ₂) ^ 4 := by ring
    calc (h₁ * h₂) ^ E1 ≤ (P ^ 2 * (σ₁ * σ₂) ^ 4) ^ E1 :=
          Real.rpow_le_rpow (mul_nonneg (by linarith) (by linarith)) hprod hE1
      _ = (P ^ 2) ^ E1 * ((σ₁ * σ₂) ^ 4) ^ E1 :=
          Real.mul_rpow (pow_nonneg hP0.le 2) (pow_nonneg hS0.le 4)
      _ = (P ^ E1) ^ 2 * (σ₁ * σ₂) ^ (4 * E1) := by
          rw [pow_rpow_eq_rpow_mul hS0.le, sq, sq, Real.mul_rpow hP0.le hP0.le]
          norm_num
  have hSck : 0 < (σ₁ * σ₂) ^ (4 * ck) := Real.rpow_pos_of_pos hS0 _
  have hXiP : 0 ≤ XiP := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hSck
    linarith
  have hC : 0 ≤ XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) :=
    mul_nonneg hXiP (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hF6) hΓ)
  calc XiH * ((h₁ * h₂) ^ E1 * F6) * Real.sqrt (l₁ * l₂)
      ≤ (XiP * (σ₁ * σ₂) ^ (4 * ck)) * ((P ^ E1) ^ 2 * (σ₁ * σ₂) ^ (4 * E1) * F6) *
          ((P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) := by
        refine mul_le_mul ?_ hsq (Real.sqrt_nonneg _) ?_
        · exact mul_le_mul hXi (mul_le_mul_of_nonneg_right hE hF6)
            (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by linarith) (by linarith)) _) hF6)
            (mul_nonneg hXiP hSck.le)
        · exact mul_nonneg (mul_nonneg hXiP hSck.le)
            (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hS0.le _)) hF6)
    _ = XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) *
          ((σ₁ * σ₂) ^ (4 * ck) * (σ₁ * σ₂) ^ (4 * E1) * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) := by
        ring
    _ = XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) *
          (σ₁ * σ₂) ^ (4 * ck + 4 * E1 + (8 * cr + a2 - dq) / 2) := by
        rw [Real.rpow_add hS0, Real.rpow_add hS0]
    _ ≤ XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) * (σ₁ * σ₂) ^ (-e) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hS1 (by linarith)) hC
    _ = XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) * (σ₁ ^ (-e) * σ₂ ^ (-e)) := by
        rw [Real.mul_rpow hσ₁0.le hσ₂0.le]
end Formalism.MainNotions.BridgeLemma₂
