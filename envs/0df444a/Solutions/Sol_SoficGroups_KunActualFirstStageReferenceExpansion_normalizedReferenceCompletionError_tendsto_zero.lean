-- Prove2me | solution 1 for SoficGroups.KunActualFirstStageReferenceExpansion.normalizedReferenceCompletionError_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/5a50ba54-4328-40c9-b674-b22883a29b95

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunActualFirstStageReferenceExpansion
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (C : (n : ℕ) → Finset (V n))
    (σref σact : (n : ℕ) → ι → Equiv.Perm (V n))
    (hboundary : Tendsto
      (fun n =>
        (SoficGroups.boundary (σref n) (C n) : ℝ) /
          (C n).card)
      atTop (nhds 0))
    (hdisagreement : Tendsto
      (fun n =>
        (componentGeneratorDisagreement
          (C n) (σref n) (σact n) : ℝ) / (C n).card)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        normalizedReferenceCompletionError (C n) (σref n) (σact n))
      atTop (nhds 0) := by
  have hsum :=
    hboundary.add (hdisagreement.const_mul (2 : ℝ))
  simpa only [normalizedReferenceCompletionError, add_div,
    mul_div_assoc, zero_add, mul_zero] using hsum
end SoficGroups.KunActualFirstStageReferenceExpansion
