-- Prove2me | solution 1 for Stallings.foldedMembershipTest_eq_true_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:16:50.291961+00:00
-- url     : https://prove2.me/submissions/77018a51-7672-4514-af03-5605a5d10e6a

import Definitions.Def_Stallings_Folding
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Definitions.Def_Stallings_Flower
import Theorems.Thm_Stallings_foldWords_loopSubgroup_eq_generatorSubgroup
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff



set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution (S : List Word) (g : Free) :
    foldedMembershipTest S g = true ↔ g ∈ generatorSubgroup S := by
  change (foldWords S).membershipTest g = true ↔ g ∈ generatorSubgroup S
  rw [InverseAutomaton.membershipTest_eq_true_iff,
    foldWords_loopSubgroup_eq_generatorSubgroup]
end Stallings
