-- Prove2me | solution 1 for SupplierAudit.Joint.aggProfit_displays
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:16:40.38686+00:00
-- url     : https://prove2.me/submissions/dcc4c181-7f67-40cd-ae19-20e7ae9f1934

import Mathlib
import Definitions.Def_SupplierAudit_Joint_Model

open SupplierAudit.Joint in
theorem solution (P : SupplierAudit.Competition.Params) (K y z : ℝ) :
    aggProfit P K (0, y, 0) = expProfit₁ P K 0 y 0 0 + expProfit₂ P K 0 0 0 y ∧
    aggProfit P K (y, 0, 0) = expProfit₁ P K y 0 0 0 + expProfit₂ P K 0 0 y 0 ∧
    aggProfit P K (y, z, 0) = expProfit₁ P K y 0 0 z + expProfit₂ P K 0 z y 0 ∧
    aggProfit P K (y, 0, z) = expProfit₁ P K y 0 z 0 + expProfit₂ P K z 0 y 0 := by
  have h0 : SupplierAudit.Competition.auditCost P K 0 = 0 := by
    simp [SupplierAudit.Competition.auditCost]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [aggProfit, jointG₁, jointG₂, totalCost, expProfit₁, expProfit₂,
      SupplierAudit.Competition.lamC, h0, sub_zero, mul_one]
    ring
