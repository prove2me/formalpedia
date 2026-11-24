-- Prove2me | solution 1 for Stallings.CosetEquivalent.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:12:50.340854+00:00
-- url     : https://prove2.me/submissions/f4309571-d9d7-4453-b1d7-b16068ddbc40

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
    (gh : CosetEquivalent H g h) : CosetEquivalent H h g := by
  change g * h⁻¹ ∈ H at gh
  change h * g⁻¹ ∈ H
  simpa using H.inv_mem gh
end Stallings.CosetEquivalent
