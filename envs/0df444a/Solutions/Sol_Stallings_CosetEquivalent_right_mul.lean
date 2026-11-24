-- Prove2me | solution 1 for Stallings.CosetEquivalent.right_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:12:38.618025+00:00
-- url     : https://prove2.me/submissions/a6284afd-5520-4b4d-ac2d-3f649fce39be

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
    (gh : CosetEquivalent H g h) (x : Free) : CosetEquivalent H (g * x) (h * x) := by
  change g * h⁻¹ ∈ H at gh
  change (g * x) * (h * x)⁻¹ ∈ H
  simpa [mul_assoc] using gh
end Stallings.CosetEquivalent
