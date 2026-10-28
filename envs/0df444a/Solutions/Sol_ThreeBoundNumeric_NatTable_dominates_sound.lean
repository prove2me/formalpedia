-- Prove2me | solution 1 for ThreeBoundNumeric.NatTable.dominates_sound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:43:07.902816+00:00
-- url     : https://prove2.me/submissions/74b910f9-3f32-4e75-9746-27bd223c769d

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_FlatProfiles
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NatTableChecks
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures


section
/- Small structural checks for globally ordered piecewise constant tables. -/


set_option autoImplicit false

namespace ThreeBoundNumeric.NatTable

theorem bool_and_true (a b : Bool) : ((a && b)=true) ↔ (a=true ∧ b=true) := by
  cases a <;> cases b <;> decide









end ThreeBoundNumeric.NatTable



end

section
set_option autoImplicit false
namespace ThreeBoundNumeric
end ThreeBoundNumeric
open ThreeBoundNumeric
namespace ThreeBoundNumeric.NatTable
end ThreeBoundNumeric.NatTable
open ThreeBoundNumeric.NatTable

theorem solution (factor : ℕ) (a b : NatTable)
    (h : dominates factor a b=true) : ∀ i, a.get i≤factor*b.get i := by
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
end
