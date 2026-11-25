-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__mul_sqrt_div_mul_sqrt_div_le_a87fee8277d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:45:15.248909+00:00
-- url     : https://prove2.me/submissions/57737584-cd24-4d1a-9f2e-943e2c4e7580

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsNum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsOneN
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rpow_le_rpow_mul_rpow_133b1c2bea84
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.MainNotions.BridgeLemma₂
private theorem le_of_sq_le_sq_of_nonneg' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [mul_self_nonneg (a - b)]
private theorem sq_le_pow_four_of_one_le {x : ℝ} (hx : 1 ≤ x) : x ^ 2 ≤ x ^ 4 := by
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)]
private theorem rpow_product_le_rpow_neg_sq_with_a4 {σ cS c4 cV a2 a4 dq e : ℝ} (hσ : 1 ≤ σ) (hcS : 0 ≤ cS)
    (he : 4 * c4 + 4 * cS + 4 * cV + a2 / 2 + |a4| - dq / 2 ≤ -e) :
    σ ^ (4 * cS) * (σ ^ (4 * c4)) ^ 2 * (σ ^ (4 * cV)) ^ 2 * (σ ^ a2 * (σ ^ a4) ^ 2 * σ ^ (-dq)) ≤
      (σ ^ (-e)) ^ 2 := by
  have h0 : 0 < σ := by linarith
  have hsq : ∀ x : ℝ, (σ ^ x) ^ 2 = σ ^ (2 * x) := fun x => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, mul_comm] <;> norm_num
  simp only [hsq, ← Real.rpow_add h0]
  apply Real.rpow_le_rpow_of_exponent_le hσ
  linarith [le_abs_self a4]
private theorem rpow_product_le_rpow_neg_sq {σ cS c4 cV a2 a4 dq e : ℝ} (hσ : 1 ≤ σ) (hcS : 0 ≤ cS)
    (he : 4 * c4 + 4 * cS + 4 * cV + a2 / 2 + |a4| - dq / 2 ≤ -e) :
    σ ^ (4 * cS) * (σ ^ (4 * c4)) ^ 2 * (σ ^ (4 * cV)) ^ 2 * (σ ^ a2 * σ ^ (-dq)) ≤
      (σ ^ (-e)) ^ 2 := by
  have h0 : 0 < σ := by linarith
  have hsq : ∀ x : ℝ, (σ ^ x) ^ 2 = σ ^ (2 * x) := fun x => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, mul_comm] <;> norm_num
  simp only [hsq, ← Real.rpow_add h0]
  apply Real.rpow_le_rpow_of_exponent_le hσ
  linarith [abs_nonneg a4]
end Formalism.MainNotions.BridgeLemma₂
end

set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
set_option maxHeartbeats 800000
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {P σ₁ σ₂ hS₁ hS₂ h4₁ h4₂ hV₁ hV₂ cS c4 cV Γ Ex a2 a4 dq τ Q n₁ n₂ K4 N L₁ L₂ e : ℝ}
    (hP : 1 ≤ P) (hσ₁ : 1 ≤ σ₁) (hσ₂ : 1 ≤ σ₂)
    (hS1₁ : 1 ≤ hS₁) (hS1₂ : 1 ≤ hS₂) (h41₁ : 1 ≤ h4₁) (h41₂ : 1 ≤ h4₂) (hV1₁ : 1 ≤ hV₁) (hV1₂ : 1 ≤ hV₂)
    (hSP₁ : hS₁ ≤ P * σ₁ ^ 4) (hSP₂ : hS₂ ≤ P * σ₂ ^ 4) (h4P₁ : h4₁ ≤ P * σ₁ ^ 4) (h4P₂ : h4₂ ≤ P * σ₂ ^ 4)
    (hVP₁ : hV₁ ≤ P * σ₁ ^ 4) (hVP₂ : hV₂ ≤ P * σ₂ ^ 4) (hcS : 0 ≤ cS) (hc4 : 0 ≤ c4) (hcV : 0 ≤ cV)
    (hΓ : 0 ≤ Γ) (hEx : 0 ≤ Ex) (hτ : 0 ≤ τ) (hQ : 0 ≤ Q) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hK4 : 0 ≤ K4)
    (hN₁ : N ≤ hS₁ ^ cS * n₁ * (K4 * (h4₁ * h4₂) ^ c4)) (hN₂ : N ≤ hS₂ ^ cS * n₂ * (K4 * (h4₂ * h4₁) ^ c4))
    (hL₁ : L₁ = (hV₁ ^ cV) ^ 2 * (Γ * σ₁ ^ a2) * (Ex * σ₁ ^ a4) ^ 2 * τ * Q * σ₁ ^ (-dq))
    (hL₂ : L₂ = (hV₂ ^ cV) ^ 2 * (Γ * σ₂ ^ a2) * σ₂ ^ (-dq) * τ)
    (he : 4 * c4 + 4 * cS + 4 * cV + a2 / 2 + |a4| - dq / 2 ≤ -e) :
    N * (Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂)) ≤
      (K4 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) * Γ * Ex * τ * Real.sqrt Q) * (σ₁ ^ (-e) * σ₂ ^ (-e)) := by
  have hσ₁0 : 0 < σ₁ := by linarith
  have hσ₂0 : 0 < σ₂ := by linarith
  have hS0₁ : 0 < hS₁ := by linarith
  have hS0₂ : 0 < hS₂ := by linarith
  have h40₁ : 0 < h4₁ := by linarith
  have h40₂ : 0 < h4₂ := by linarith
  have hV0₁ : 0 < hV₁ := by linarith
  have hV0₂ : 0 < hV₂ := by linarith
  have hP0 : 0 < P := by linarith
  have hL0₁ : 0 ≤ L₁ := by rw [hL₁]; positivity
  have hL0₂ : 0 ≤ L₂ := by rw [hL₂]; positivity
  have hs0 : 0 ≤ Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂) := by positivity
  have hR0 : 0 ≤ (K4 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) * Γ * Ex * τ * Real.sqrt Q) *
      (σ₁ ^ (-e) * σ₂ ^ (-e)) := by positivity
  by_cases hN : N ≤ 0
  · have h1 : 0 ≤ (-N) * (Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂)) := mul_nonneg (by linarith) hs0
    linarith
  push_neg at hN
  apply le_of_sq_le_sq_of_nonneg' hR0
  have hlhs : (N * (Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂))) ^ 2 = N ^ 2 * (L₁ / n₁ * (L₂ / n₂)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hL0₁ hn₁.le), Real.sq_sqrt (div_nonneg hL0₂ hn₂.le)]
  have hrhs : ((K4 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) * Γ * Ex * τ * Real.sqrt Q) *
      (σ₁ ^ (-e) * σ₂ ^ (-e))) ^ 2 = K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q *
      ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 * ((σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2) := by
    have hq := Real.sq_sqrt hQ
    linear_combination (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 *
      ((σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2)) * hq
  rw [hlhs, hrhs]
  have e1 : n₁ * (L₁ / n₁) = L₁ := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hn₁.ne', mul_one]
  have e2 : n₂ * (L₂ / n₂) = L₂ := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hn₂.ne', mul_one]
  have hN2 : N ^ 2 ≤ (hS₁ ^ cS * n₁ * (K4 * (h4₁ * h4₂) ^ c4)) * (hS₂ ^ cS * n₂ * (K4 * (h4₂ * h4₁) ^ c4)) := by
    rw [sq]; exact mul_le_mul hN₁ hN₂ hN.le (by positivity)
  have b1 := rpow_le_rpow_mul_rpow hP hσ₁ hS1₁ hSP₁ hcS
  have b2 := rpow_le_rpow_mul_rpow hP hσ₂ hS1₂ hSP₂ hcS
  have b3 := rpow_le_rpow_mul_rpow hP hσ₁ h41₁ h4P₁ hc4
  have b4 := rpow_le_rpow_mul_rpow hP hσ₂ h41₂ h4P₂ hc4
  have b5 := rpow_le_rpow_mul_rpow hP hσ₁ hV1₁ hVP₁ hcV
  have b6 := rpow_le_rpow_mul_rpow hP hσ₂ hV1₂ hVP₂ hcV
  have hPp : (P ^ cS) ^ 2 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4 ≤ ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 := by
    have hx : 1 ≤ P ^ cS := Real.one_le_rpow hP hcS
    have h2 : (P ^ cS) ^ 2 ≤ (P ^ cS) ^ 4 := sq_le_pow_four_of_one_le hx
    calc (P ^ cS) ^ 2 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4 ≤ (P ^ cS) ^ 4 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)
      _ = ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 := by ring
  have hσ1b := rpow_product_le_rpow_neg_sq_with_a4 hσ₁ hcS he
  have hσ2b := rpow_product_le_rpow_neg_sq hσ₂ hcS he
  calc N ^ 2 * (L₁ / n₁ * (L₂ / n₂))
      ≤ ((hS₁ ^ cS * n₁ * (K4 * (h4₁ * h4₂) ^ c4)) * (hS₂ ^ cS * n₂ * (K4 * (h4₂ * h4₁) ^ c4))) *
          (L₁ / n₁ * (L₂ / n₂)) := mul_le_mul_of_nonneg_right hN2 (by positivity)
    _ = K4 ^ 2 * (hS₁ ^ cS * hS₂ ^ cS) * (h4₁ ^ c4 * h4₂ ^ c4) ^ 2 * (n₁ * (L₁ / n₁)) *
          (n₂ * (L₂ / n₂)) := by
        rw [mul_comm h4₂ h4₁, Real.mul_rpow h40₁.le h40₂.le]; ring
    _ = K4 ^ 2 * (hS₁ ^ cS * hS₂ ^ cS) * (h4₁ ^ c4 * h4₂ ^ c4) ^ 2 * L₁ * L₂ := by rw [e1, e2]
    _ = (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * ((hS₁ ^ cS * hS₂ ^ cS) * (h4₁ ^ c4 * h4₂ ^ c4) ^ 2 *
          (hV₁ ^ cV) ^ 2 * (hV₂ ^ cV) ^ 2 * (σ₁ ^ a2 * (σ₁ ^ a4) ^ 2 * σ₁ ^ (-dq)) *
          (σ₂ ^ a2 * σ₂ ^ (-dq))) := by
        rw [hL₁, hL₂]; ring
    _ ≤ (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * (((P ^ cS * σ₁ ^ (4 * cS)) * (P ^ cS * σ₂ ^ (4 * cS))) *
          ((P ^ c4 * σ₁ ^ (4 * c4)) * (P ^ c4 * σ₂ ^ (4 * c4))) ^ 2 *
          (P ^ cV * σ₁ ^ (4 * cV)) ^ 2 * (P ^ cV * σ₂ ^ (4 * cV)) ^ 2 *
          (σ₁ ^ a2 * (σ₁ ^ a4) ^ 2 * σ₁ ^ (-dq)) * (σ₂ ^ a2 * σ₂ ^ (-dq))) := by
        gcongr
    _ = (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * (((P ^ cS) ^ 2 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4) *
          (σ₁ ^ (4 * cS) * (σ₁ ^ (4 * c4)) ^ 2 * (σ₁ ^ (4 * cV)) ^ 2 * (σ₁ ^ a2 * (σ₁ ^ a4) ^ 2 * σ₁ ^ (-dq))) *
          (σ₂ ^ (4 * cS) * (σ₂ ^ (4 * c4)) ^ 2 * (σ₂ ^ (4 * cV)) ^ 2 * (σ₂ ^ a2 * σ₂ ^ (-dq)))) := by
        ring
    _ ≤ (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * (((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 *
          (σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul hPp hσ1b (by positivity) (by positivity)) hσ2b (by positivity)
          (by positivity)
    _ = K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 *
          ((σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2) := by ring
end Formalism.MainNotions.BridgeLemma₂
