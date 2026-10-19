-- Prove2me | solution 1 for PermanentRollout.sourceFreeAffineFormFiniteLinearCombination_gate_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/e522aac6-032d-4b43-a7b4-bd4c55e59ed8

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {ι α : Type*} [Fintype α]
    (coefficient : α → ℂ) (form : α → FreeAffineForm ι)
    (bound : ℕ)
    (hform : ∀ j i, (form j).gateCoefficients i ≠ 0 → i < bound) :
    ∀ i,
      (sourceFreeAffineFormFiniteLinearCombination coefficient form).gateCoefficients i ≠ 0 →
        i < bound := by
  intro i hi
  by_contra hbound
  have hzero : ∀ j, (form j).gateCoefficients i = 0 := by
    intro j
    by_contra hj
    exact hbound (hform j i hj)
  apply hi
  simp [sourceFreeAffineFormFiniteLinearCombination, hzero]
end PermanentRollout
