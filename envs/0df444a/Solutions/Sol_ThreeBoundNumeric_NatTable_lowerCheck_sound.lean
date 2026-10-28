-- Prove2me | solution 1 for ThreeBoundNumeric.NatTable.lowerCheck_sound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:43:08.515357+00:00
-- url     : https://prove2.me/submissions/5713a979-4bfe-4dc8-a42e-8667c4a78ac7

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

theorem solution (bound : ℕ) (table : NatTable)
    (h : lowerCheck bound table=true) : ∀ i, bound≤table.get i := by
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
end
