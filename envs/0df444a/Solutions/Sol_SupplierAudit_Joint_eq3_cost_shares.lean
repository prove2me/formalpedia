-- Prove2me | solution 1 for SupplierAudit.Joint.eq3_cost_shares
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:48:11.35739+00:00
-- url     : https://prove2.me/submissions/c862ddb3-4938-491a-bf5c-bfdb1febadb0

import Mathlib
import Definitions.Def_SupplierAudit_Joint_Model

open SupplierAudit.Joint

theorem solution (P : SupplierAudit.Competition.Params) (K : ℝ) (x : ℝ × ℝ × ℝ) :
    Gamma₁ P K x + Gamma₂ P K x = totalCost P K x ∧
    jointG₁ P x - Gamma₁ P K x = jointG₂ P x - Gamma₂ P K x ∧
    jointG₁ P x - Gamma₁ P K x = aggProfit P K x / 2 ∧
    (x.2.2 = 0 →
      Gamma₁ P K x = (1 / 2) * ((SupplierAudit.Competition.auditCost P K x.1 + SupplierAudit.Competition.auditCost P K x.2.1) + deltaPi P x) ∧
      Gamma₂ P K x = (1 / 2) * ((SupplierAudit.Competition.auditCost P K x.1 + SupplierAudit.Competition.auditCost P K x.2.1) - deltaPi P x)) := by
  have h0 : SupplierAudit.Competition.auditCost P K 0 = 0 := by
    simp [SupplierAudit.Competition.auditCost]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Gamma₁ Gamma₂; ring
  · unfold Gamma₁ Gamma₂ deltaPi; ring
  · unfold Gamma₁ aggProfit deltaPi; ring
  · intro h
    unfold Gamma₁ Gamma₂ totalCost
    rw [h, h0, add_zero]
    exact ⟨rfl, rfl⟩
