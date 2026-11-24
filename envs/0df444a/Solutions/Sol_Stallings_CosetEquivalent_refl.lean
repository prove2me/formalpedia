-- Prove2me | solution 1 for Stallings.CosetEquivalent.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:12:49.625315+00:00
-- url     : https://prove2.me/submissions/51d37a01-7fb7-4d8e-b274-4f9f94e5a0c9

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff



set_option autoImplicit true
open Stallings
open Stallings.CosetEquivalent
namespace Stallings.CosetEquivalent
theorem _root_.solution (H : Subgroup Free) (g : Free) : CosetEquivalent H g g := by
  simp [CosetEquivalent]
end Stallings.CosetEquivalent
