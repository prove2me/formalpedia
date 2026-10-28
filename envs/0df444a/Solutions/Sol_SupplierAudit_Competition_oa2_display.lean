-- Prove2me | solution 1 for SupplierAudit.Competition.oa2_display
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:26:32.217042+00:00
-- url     : https://prove2.me/submissions/acf83518-fba7-472f-ba94-db49043eee0a

import Mathlib
import Definitions.Def_SupplierAudit_Competition_Model

open SupplierAudit.Competition


theorem solution (P : Params) (K e11 e1c e22 e2c : ℝ)
    (h11 : e11 ∈ Set.Icc (0 : ℝ) 1) (h1c : e1c ∈ Set.Icc (0 : ℝ) 1)
    (h22 : e22 ∈ Set.Icc (0 : ℝ) 1) (h2c : e2c ∈ Set.Icc (0 : ℝ) 1) :
    expProfit₁ P K e11 e1c e22 e2c =
      (1 - lamI P e11) * (1 - lamC P e1c e2c) * (1 - lamI P e22) *
          ((P.α - 2 * P.w) / (2 + P.β)) ^ 2
      + (1 - lamI P e11) * (1 - lamC P e1c e2c) * lamI P e22 *
          (P.α / (2 + P.β) + (P.β * P.dM - (4 - P.β) * P.w + P.β * P.wh) / (4 - P.β ^ 2)) ^ 2
      + lamI P e11 * (1 - lamC P e1c e2c) * (1 - lamI P e22) *
          (P.α / (2 + P.β) - (2 * P.dM + 2 * (1 - P.β) * P.w + 2 * P.wh) / (4 - P.β ^ 2)) ^ 2
      + ((1 - lamI P e11) * lamC P e1c e2c * (1 - lamI P e22)
          + lamI P e11 * (1 - lamC P e1c e2c) * lamI P e22) *
          ((P.α - P.dM - P.w - P.wh) / (2 + P.β)) ^ 2
      + (1 - lamI P e11) * lamC P e1c e2c * lamI P e22 *
          ((P.α - P.dM) / (2 + P.β) - (2 * P.w + 2 * (1 - P.β) * P.wh) / (4 - P.β ^ 2)) ^ 2
      + lamI P e11 * lamC P e1c e2c * (1 - lamI P e22) *
          ((P.α - P.dM) / (2 + P.β) - ((4 - P.β) * P.wh - P.β * P.w) / (4 - P.β ^ 2)) ^ 2
      + lamI P e11 * lamC P e1c e2c * lamI P e22 *
          ((P.α - P.dM - 2 * P.wh) / (2 + P.β)) ^ 2
      - ((if 0 < e11 then K else 0) + P.a / 2 * e11 ^ 2)
      - ((if 0 < e1c then K else 0) + P.a / 2 * e1c ^ 2) := by
  have hb0 := P.hβ0
  have hb1 := P.hβ1
  have h2p : (2 + P.β) ≠ 0 := by linarith
  have h2m : (2 - P.β) ≠ 0 := by linarith
  have h4 : (4 - P.β ^ 2) ≠ 0 := by nlinarith
  have hI0 : intercept P 0 = P.α := by simp [intercept]
  have hI1 : intercept P 1 = P.α - P.dM := by simp [intercept]
  have hI2 : intercept P 2 = P.α - P.dM := by simp [intercept]
  have hc0 : unitCost P 0 = 2 * P.w := by simp [unitCost]
  have hc1 : unitCost P 1 = P.w + P.wh := by simp [unitCost] <;> ring
  have hc2 : unitCost P 2 = 2 * P.wh := by simp [unitCost] <;> ring
  have q00 : stage2Profit P 0 0 = ((P.α - 2 * P.w) / (2 + P.β)) ^ 2 := by
    unfold stage2Profit stage2q; rw [hI0, hc0]; congr 1; field_simp <;> ring
  have q01 : stage2Profit P 0 1 =
      (P.α / (2 + P.β) + (P.β * P.dM - (4 - P.β) * P.w + P.β * P.wh) / (4 - P.β ^ 2)) ^ 2 := by
    unfold stage2Profit stage2q; rw [hI0, hc0, hI1, hc1]; congr 1; field_simp <;> ring
  have q10 : stage2Profit P 1 0 =
      (P.α / (2 + P.β) - (2 * P.dM + 2 * (1 - P.β) * P.w + 2 * P.wh) / (4 - P.β ^ 2)) ^ 2 := by
    unfold stage2Profit stage2q; rw [hI0, hc0, hI1, hc1]; congr 1; field_simp <;> ring
  have q11 : stage2Profit P 1 1 = ((P.α - P.dM - P.w - P.wh) / (2 + P.β)) ^ 2 := by
    unfold stage2Profit stage2q; rw [hI1, hc1]; congr 1; field_simp <;> ring
  have q12 : stage2Profit P 1 2 =
      ((P.α - P.dM) / (2 + P.β) - (2 * P.w + 2 * (1 - P.β) * P.wh) / (4 - P.β ^ 2)) ^ 2 := by
    unfold stage2Profit stage2q; rw [hI1, hc1, hI2, hc2]; congr 1; field_simp <;> ring
  have q21 : stage2Profit P 2 1 =
      ((P.α - P.dM) / (2 + P.β) - ((4 - P.β) * P.wh - P.β * P.w) / (4 - P.β ^ 2)) ^ 2 := by
    unfold stage2Profit stage2q; rw [hI1, hc1, hI2, hc2]; congr 1; field_simp <;> ring
  have q22 : stage2Profit P 2 2 = ((P.α - P.dM - 2 * P.wh) / (2 + P.β)) ^ 2 := by
    unfold stage2Profit stage2q; rw [hI2, hc2]; congr 1; field_simp <;> ring
  unfold expProfit₁ auditCost
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, if_true, if_false, Bool.toNat_true,
    Bool.toNat_false]
  norm_num only [q00, q01, q10, q11, q12, q21, q22]
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring
