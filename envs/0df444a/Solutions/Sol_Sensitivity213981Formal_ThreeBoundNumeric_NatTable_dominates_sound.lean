-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundNumeric.NatTable.dominates_sound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:48.395822+00:00
-- url     : https://prove2.me/submissions/75df2730-bdac-423e-aa8a-5edd9c543605

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







theorem dominates_sound (factor : ℕ) (a b : NatTable)
    (h : dominates factor a b=true) : ∀ i, a.get i≤ factor*b.get i := by
  induction a generalizing b with
  | leaf av =>
      induction b with
      | leaf bv =>
          rw [dominates] at h
          exact fun _=>of_decide_eq_true h
      | branch cb lb rb hl hr =>
          rw [dominates] at h
          have hh : dominates factor (.leaf av) lb=true ∧ dominates factor (.leaf av) rb=true :=
            (bool_and_true _ _).mp h
          intro i
          simp only [NatTable.get]
          split_ifs
          · exact hl hh.1 i
          · exact hr hh.2 i
  | branch ca la ra hl hr =>
      cases b with
      | leaf bv =>
          rw [dominates] at h
          have hh : dominates factor la (.leaf bv)=true ∧ dominates factor ra (.leaf bv)=true :=
            (bool_and_true _ _).mp h
          intro i
          simp only [NatTable.get]
          split_ifs
          · exact hl _ hh.1 i
          · exact hr _ hh.2 i
      | branch cb lb rb =>
          rw [dominates] at h
          have hh : (ca==cb && dominates factor la lb)=true ∧ dominates factor ra rb=true :=
            (bool_and_true _ _).mp h
          have hleft := (bool_and_true _ _).mp hh.1
          have heq : ca=cb := by simpa using hleft.1
          subst cb
          intro i
          simp only [NatTable.get]
          split_ifs
          · exact hl _ hleft.2 i
          · exact hr _ hh.2 i

end ThreeBoundNumeric.NatTable



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (factor : Nat) (a b : Sensitivity213981Formal.ThreeBoundNumeric.NatTable)
  (h : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.dominates factor a b) Bool.true) (i : Nat),
  @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get a i)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) factor
      (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get b i)) := @Sensitivity213981Formal.ThreeBoundNumeric.NatTable.dominates_sound
