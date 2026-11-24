-- Prove2me | solution 1 for Stallings.CosetEquivalent.mem_of_mem_and_rel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:12:59.535769+00:00
-- url     : https://prove2.me/submissions/d039964b-81f0-4959-bfc2-ae9dee2e9b61

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
theorem _root_.solution {H : Subgroup Free} {g h : Free}
    (hgh : CosetEquivalent H g h) (hg : g ∈ H) : h ∈ H := by
  change g * h⁻¹ ∈ H at hgh
  have hhinv : h⁻¹ ∈ H := by
    have hm := H.mul_mem (H.inv_mem hg) hgh
    simpa [mul_assoc] using hm
  simpa using H.inv_mem hhinv
end Stallings.CosetEquivalent
