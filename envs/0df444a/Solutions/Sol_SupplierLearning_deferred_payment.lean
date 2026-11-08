-- Prove2me | solution 1 for SupplierLearning.deferred_payment
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:32:23.707474+00:00
-- url     : https://prove2.me/submissions/d6839c26-4998-47dc-b3df-f8ac75004f9c

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_stagePayoff
import Definitions.Def_SupplierLearning_Params_supplierPayoff
import Definitions.Def_SupplierLearning_Params_U
import Definitions.Def_SupplierLearning_Params_rent
import Definitions.Def_SupplierLearning_Params_deferredTerm

open SupplierLearning in
theorem solution (P : Params) (hP : P.Standing) {q y z : ℝ} (hq : 0 ≤ q) (hzy : z ≤ y)
    (hcap : (P.rh - P.rl) * q ≤ P.ch - P.cl) {φ : Contract} (hφ : φ .h = P.deferredTerm q y z) :
    P.U φ .h = 0 ∧
    P.stagePayoff .h true (φ .h) false ≤ P.stagePayoff .h true (φ .h) true ∧
    P.stagePayoff .h false (φ .h) true ≤ P.stagePayoff .h false (φ .h) false ∧
    P.supplierPayoff φ .l .h = P.rent q y z := by
  have hrh := hP.rh_pos
  have e1 : P.stagePayoff .h true (φ .h) true = P.rh * q * z := by
    rw [hφ]
    simp only [Params.stagePayoff, Params.learnedCost, Params.deferredTerm, Params.cost,
      Params.rate, outcomeValue]
    ring
  have e2 : P.stagePayoff .h true (φ .h) false = P.rh * q * z := by
    rw [hφ]
    simp only [Params.stagePayoff, Params.learnedCost, Params.deferredTerm, Params.cost,
      Params.rate, outcomeValue]
    ring
  have e3 : P.stagePayoff .h false (φ .h) true = P.rh * q * (z - y) := by
    rw [hφ]
    simp only [Params.stagePayoff, Params.learnedCost, Params.deferredTerm, Params.cost,
      Params.rate, outcomeValue]
    ring
  have e4 : P.stagePayoff .h false (φ .h) false = 0 := by
    rw [hφ]
    simp only [Params.stagePayoff, Params.learnedCost, Params.deferredTerm, Params.cost,
      Params.rate, outcomeValue]
    ring
  have e5 : P.stagePayoff .l true (φ .h) true =
      (P.ch - P.cl + (P.rl - P.rh) * q) * y + P.rh * q * z := by
    rw [hφ]
    simp only [Params.stagePayoff, Params.learnedCost, Params.deferredTerm, Params.cost,
      Params.rate, outcomeValue]
    ring
  have e6 : P.stagePayoff .l true (φ .h) false = (P.ch - P.cl + P.rl * q) * z := by
    rw [hφ]
    simp only [Params.stagePayoff, Params.learnedCost, Params.deferredTerm, Params.cost,
      Params.rate, outcomeValue]
    ring
  have e7 : P.stagePayoff .l false (φ .h) true = (P.ch - P.cl - P.rh * q) * y + P.rh * q * z := by
    rw [hφ]
    simp only [Params.stagePayoff, Params.learnedCost, Params.deferredTerm, Params.cost,
      Params.rate, outcomeValue]
    ring
  have e8 : P.stagePayoff .l false (φ .h) false = (P.ch - P.cl) * z := by
    rw [hφ]
    simp only [Params.stagePayoff, Params.learnedCost, Params.deferredTerm, Params.cost,
      Params.rate, outcomeValue]
    ring
  have hp1 : (φ .h).p₁ = P.ch * q - P.δ * P.ρ * P.rh * q * z := by rw [hφ]; rfl
  have hq1 : (φ .h).q₁ = q := by rw [hφ]; rfl
  have hneg : P.rh * q * (z - y) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hrh.le hq) (by linarith)
  refine ⟨?_, by rw [e1, e2], by rw [e3, e4]; exact hneg, ?_⟩
  · simp only [Params.U, Params.supplierPayoff, Params.expectOutcome]
    rw [e1, e2, e3, e4, hp1, hq1, max_self, max_eq_left hneg]
    simp only [Params.cost]
    ring
  · simp only [Params.supplierPayoff, Params.expectOutcome]
    rw [e5, e6, e7, e8, hp1, hq1]
    have hT : (P.ch - P.cl + P.rl * q) * z ≤ (P.ch - P.cl + (P.rl - P.rh) * q) * y + P.rh * q * z := by
      have h1 : 0 ≤ P.ch - P.cl + (P.rl - P.rh) * q := by linarith
      nlinarith [mul_nonneg h1 (sub_nonneg.mpr hzy)]
    rw [max_eq_right hT]
    simp only [Params.cost, Params.rent, Params.deltaC, Params.deltaR]
    split_ifs with hc
    · have hF : (P.ch - P.cl - P.rh * q) * y + P.rh * q * z ≤ (P.ch - P.cl) * z := by
        have h1 : P.ch - P.cl - P.rh * q ≤ 0 := by linarith
        nlinarith [mul_nonpos_of_nonpos_of_nonneg h1 (sub_nonneg.mpr hzy)]
      rw [max_eq_left hF]
      ring
    · have hF : (P.ch - P.cl) * z ≤ (P.ch - P.cl - P.rh * q) * y + P.rh * q * z := by
        have h1 : 0 ≤ P.ch - P.cl - P.rh * q := by push_neg at hc; linarith
        nlinarith [mul_nonneg h1 (sub_nonneg.mpr hzy)]
      rw [max_eq_right hF]
      ring
