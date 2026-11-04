-- Prove2me | solution 1 for ThreeSum.RawIncidences.bucket_product_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:17.482471+00:00
-- url     : https://prove2.me/submissions/6fc6d841-627e-4d37-8f28-7022f7e90e9d

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_bucket_product_eq_sum

set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : ChoiceTuple h J) :
    leftBucket P B b t * rightBucket P d C c t =
      ((B ×ˢ C).filter fun p => globalModulus h J ∣ b p.1 % P - tupleLeft t ∧
        globalModulus h J ∣ c p.2 % P + d - tupleRight t).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  exact bucket_product_eq_sum P d B C b c t
end ThreeSum.RawIncidences
