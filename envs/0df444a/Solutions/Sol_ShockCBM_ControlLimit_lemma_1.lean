-- Prove2me | solution 1 for ShockCBM.ControlLimit.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:29:33.387415+00:00
-- url     : https://prove2.me/submissions/36d99aaa-d581-4bf4-ab8a-773fd53edbd1

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting

open MeasureTheory ShockCBM.ControlLimit Set

lemma ShockCBML1.countPart_eq (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k : ℕ) :
    countPart α β k = Real.Gamma ((k : ℝ) + α) / ((Nat.factorial k : ℝ) * Real.Gamma α) *
      (1 / (β + 1)) ^ k * (β / (β + 1)) ^ α := by
  unfold countPart
  have hG : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  have hk : (0 : ℝ) < Nat.factorial k := by exact_mod_cast Nat.factorial_pos k
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ici 0)]
  swap
  · intro x hx
    simp only [mem_Ici, not_le] at hx
    simp [ProbabilityTheory.gammaPDFReal, not_le.mpr hx]
  rw [integral_Ici_eq_integral_Ioi]
  have hcongr : ∀ x ∈ Ioi (0 : ℝ),
      Real.exp (-x) * x ^ k / (Nat.factorial k : ℝ) * ProbabilityTheory.gammaPDFReal α β x =
        β ^ α / ((Nat.factorial k : ℝ) * Real.Gamma α) *
          (x ^ (((k : ℝ) + α) - 1) * Real.exp (-((β + 1) * x))) := by
    intro x hx
    have hx : 0 < x := hx
    simp only [ProbabilityTheory.gammaPDFReal, if_pos hx.le]
    have e1 : x ^ (((k : ℝ) + α) - 1) = x ^ k * x ^ (α - 1) := by
      rw [show ((k : ℝ) + α) - 1 = (k : ℝ) + (α - 1) by ring, Real.rpow_add hx, Real.rpow_natCast]
    have e2 : Real.exp (-((β + 1) * x)) = Real.exp (-x) * Real.exp (-(β * x)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) (by positivity)]
  have hb1 : 0 < β + 1 := by linarith
  rw [Real.rpow_add (by positivity), Real.rpow_natCast, Real.div_rpow hβ.le hb1.le,
    Real.div_rpow zero_le_one hb1.le, Real.one_rpow]
  have : (β + 1) ^ α ≠ 0 := (Real.rpow_pos_of_pos hb1 α).ne'
  field_simp

theorem solution (h : ℕ → ℝ) (α β a b : ℝ) (hα : 0 < α) (hβ : 0 < β) (ha : 0 < a) (hb : 0 < b)
    (z : ℕ) :
    ∑' k : ℕ, predKernel h α β a b z k =
      ∑' k : ℕ, damagePart h a b k z *
        (Real.Gamma ((k : ℝ) + α) / ((Nat.factorial k : ℝ) * Real.Gamma α)) *
        (1 / (β + 1)) ^ k * (β / (β + 1)) ^ α := by
  congr 1; ext k
  unfold predKernel
  rw [ShockCBML1.countPart_eq α β hα hβ k]
  ring
