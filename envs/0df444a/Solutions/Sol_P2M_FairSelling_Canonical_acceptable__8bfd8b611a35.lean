-- Prove2me | solution 1 for P2M_FairSelling_Canonical_acceptable__8bfd8b611a35
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:08:38.468915+00:00
-- url     : https://prove2.me/submissions/0419ab6d-0adc-446b-9439-6d8333cc4661

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.Canonical
variable {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
omit [Fintype G]
namespace FairSelling.Canonical
theorem _root_.solution (C : Canonical w p μ t k R D) (j : Fin k) :
    t ≤ vbarSum w p (C.goods j) + C.cash j := by
  have := C.acceptable j
  simp only [cash]; linarith
end FairSelling.Canonical
