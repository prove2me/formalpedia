-- Prove2me | solution 1 for ThreeSum.Histograms.sum_histogram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:44.193479+00:00
-- url     : https://prove2.me/submissions/4886c022-da39-4b87-abfd-0b2eac67eadb

import Definitions.Def_Submission_ThreeSum_Balancing
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Definitions.Def_Submission_ThreeSum_Histograms

set_option autoImplicit false
open ThreeSum ThreeSum.Histograms
open Finset
open scoped BigOperators
variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
namespace ThreeSum.Histograms
theorem _root_.solution (I : Finset ι) (key : ι → G) (weight : ι → ℕ) :
    (∑ k, histogram I key weight k) = ∑ i ∈ I, weight i := by
  unfold histogram
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  simp
end ThreeSum.Histograms
