-- Prove2me | solution 1 for ThreeBoundRecordAllowedAlgorithm.recordAllowedFor_of
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:41:45.473085+00:00
-- url     : https://prove2.me/submissions/fc17c62a-fe34-45b1-9d02-5a87da676d7e

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2RawExpressions

namespace ThreeBoundNumeric
end ThreeBoundNumeric
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundRecordAllowedAlgorithm
end ThreeBoundRecordAllowedAlgorithm
open ThreeBoundRecordAllowedAlgorithm
open ThreeBoundNumeric

theorem solution (caps : Caps) (a c : Entry) (r : Q2Record)
    (hallowed : allowedRecord caps c.tolerance r = true)
    (hguard : ∀ k, k ≤ c.tolerance →
      k < a.tolerance → a.threshold (k+1) ≤ c.threshold k →
      r (3+k)=0 ∧ (k=0 → r 6=0) ∧ (k=1 → r 7=0))
    (hpositive : ∀ k, k ≤ c.tolerance → r k≠0 →
      c.guard ≠ (if k=0 then a.threshold k else min (a.threshold k) (c.threshold (k-1)))) :
    recordAllowedFor caps a c r = true := by
  unfold recordAllowedFor
  simp only [Bool.and_eq_true]
  constructor
  · refine ⟨hallowed,?_⟩
    apply List.all_eq_true.mpr
    intro k hk
    have hk' : k ≤ c.tolerance := Nat.le_of_lt_succ (List.mem_range.mp hk)
    by_cases he : k < a.tolerance ∧ a.threshold (k+1) ≤ c.threshold k
    · obtain ⟨hg,h0,h1⟩ := hguard k hk' he.1 he.2
      simp only [he,decide_true,Bool.not_true,Bool.false_or,hg,beq_self_eq_true,Bool.true_and]
      split_ifs with hz ho
      · simp [h0 hz]
      · simp [h1 ho]
      · rfl
    · simp [he]
  · apply List.all_eq_true.mpr
    intro k hk
    have hk' : k ≤ c.tolerance := Nat.le_of_lt_succ (List.mem_range.mp hk)
    by_cases hz : r k=0
    · simp [hz]
    · have he := hpositive k hk' hz
      simpa [hz] using he
end
