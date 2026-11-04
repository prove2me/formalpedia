-- Prove2me | solution 1 for ThreeSum.RawIncidences.rawMass_eq_sum_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:58.210981+00:00
-- url     : https://prove2.me/submissions/1dc8ee8b-9f70-41f3-9211-71c10c75ac14

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences

set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawIncidences
theorem _root_.solution (h J : ℕ) (P d : ℤ) (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) :
    rawMass h J P d T a b c =
      ∑ t ∈ T, (witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)).card :=
  Finset.card_sigma _ _
end ThreeSum.RawIncidences
