-- Prove2me | solution 1 for Stallings.CosetEquivalent.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:12:48.742201+00:00
-- url     : https://prove2.me/submissions/d43992dc-bf81-48b4-bce0-0234c173c9a9

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
theorem _root_.solution {H : Subgroup Free} {g h k : Free}
    (gh : CosetEquivalent H g h) (hk : CosetEquivalent H h k) :
    CosetEquivalent H g k := by
  change g * h⁻¹ ∈ H at gh
  change h * k⁻¹ ∈ H at hk
  change g * k⁻¹ ∈ H
  have hmul : (g * h⁻¹) * (h * k⁻¹) ∈ H := H.mul_mem gh hk
  simpa [mul_assoc] using hmul
end Stallings.CosetEquivalent
