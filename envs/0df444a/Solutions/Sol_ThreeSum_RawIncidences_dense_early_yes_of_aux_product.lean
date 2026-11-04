-- Prove2me | solution 1 for ThreeSum.RawIncidences.dense_early_yes_of_aux_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:18.921349+00:00
-- url     : https://prove2.me/submissions/53f8cd1e-063d-4ac8-aed0-4b6f8dc2cda3

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_WeightedCache3SUM_Alias_77565573dc2a8798
import Theorems.Thm_ThreeSum_Arithmetic_exists_aux_not_dvd_of_prod_bound


set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} {P d : ℤ}
    (T : Finset (Original α β γ)) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (aux : Finset ℤ) (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hcop : (aux : Set ℤ).Pairwise (fun l r => IsCoprime l r))
    (hbound : ∀ t ∈ T, difference a b c t ≠ 0 →
      (difference a b c t).natAbs < (∏ l ∈ aux, l).natAbs)
    (hlarge : representationCap h J * Arithmetic.weightedFalseCount T (difference a b c) aux P <
      rawMass h J P d T a b c) :
    ∃ t ∈ T, difference a b c t = 0 := by
  apply dense_early_yes T a b c aux hP hguard _ hlarge
  intro t ht hn
  exact Arithmetic.exists_aux_not_dvd_of_prod_bound aux (difference a b c t)
    hcop hn (hbound t ht hn)
end ThreeSum.RawIncidences
