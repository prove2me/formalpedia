-- Prove2me | solution 1 for ThreeSum.Histograms.selected_pairMass_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:38.120022+00:00
-- url     : https://prove2.me/submissions/a3238a9a-283d-4e50-bdc2-c07ffbaad5ab

import Definitions.Def_Submission_ThreeSum_Balancing
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Definitions.Def_Submission_ThreeSum_Histograms
import Theorems.Thm_ThreeSum_Histograms_sum_histogram
import Definitions.Def_WeightedCache3SUM_Alias_6d2ffa19c0cd121d
import Theorems.Thm_ThreeSum_Balancing_chooseOffset_balanced


set_option autoImplicit false
open ThreeSum ThreeSum.Histograms
open Finset
open scoped BigOperators
variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
namespace ThreeSum.Histograms
theorem _root_.solution [Inhabited G]
    (keys : List G) (hkeys : ∀ d, d ∈ keys)
    (I : Finset ι) (J : Finset τ) (left : ι → G) (right : τ → G)
    (weightL : ι → ℕ) (weightR : τ → ℕ) :
    Fintype.card G * pairMass I J left right weightL weightR
      (Balancing.chooseOffset keys (histogram J right weightR) (histogram I left weightL)) ≤
        (∑ i ∈ I, weightL i) * (∑ j ∈ J, weightR j) := by
  have h := Balancing.chooseOffset_balanced keys hkeys
    (histogram J right weightR) (histogram I left weightL)
  rw [correlation_histograms, sum_histogram, sum_histogram] at h
  simpa only [Nat.mul_comm] using h
end ThreeSum.Histograms
