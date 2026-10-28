-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundNumeric.NatTable.lowerCheck_sound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:58.904971+00:00
-- url     : https://prove2.me/submissions/23d9f216-6c1c-4d2f-bcbf-5a2c33fbe79e

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_NatTableChecks
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section
/- Small structural checks for globally ordered piecewise constant tables. -/


set_option autoImplicit false

namespace ThreeBoundNumeric.NatTable

theorem bool_and_true (a b : Bool) : ((a && b)=true) ↔ (a=true ∧ b=true) := by
  cases a <;> cases b <;> decide



theorem lowerCheck_sound (bound : ℕ) (table : NatTable)
    (h : lowerCheck bound table=true) : ∀ i, bound≤ table.get i := by
  induction table with
  | leaf v =>
      intro i
      exact of_decide_eq_true h
  | branch cut left right hl hr =>
      have hh : lowerCheck bound left=true ∧ lowerCheck bound right=true := (bool_and_true _ _).mp h
      intro i
      simp only [NatTable.get]
      split_ifs
      · exact hl hh.1 i
      · exact hr hh.2 i





end ThreeBoundNumeric.NatTable



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (bound : Nat) (table : Sensitivity213981Formal.ThreeBoundNumeric.NatTable)
  (h : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.lowerCheck bound table) Bool.true) (i : Nat),
  @LE.le.{0} Nat instLENat bound (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get table i) := @Sensitivity213981Formal.ThreeBoundNumeric.NatTable.lowerCheck_sound
