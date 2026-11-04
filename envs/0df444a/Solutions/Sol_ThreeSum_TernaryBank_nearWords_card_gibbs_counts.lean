-- Prove2me | solution 1 for ThreeSum.TernaryBank.nearWords_card_gibbs_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:18.351463+00:00
-- url     : https://prove2.me/submissions/fe7e34a8-cb74-4a08-a16c-f22140a8501c

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Theorems.Thm_ThreeSum_TernaryBank_deficit_product_eq_counts
import Theorems.Thm_ThreeSum_TernaryBank_nearWords_card_gibbs

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (nearWords Q D).card * z ^ D ≤
      (1 + z) ^ digitCount Q 1 * (1 + z + z ^ 2) ^ digitCount Q 2 := by
  rw [← deficit_product_eq_counts]
  exact nearWords_card_gibbs Q D z hz hz1
end ThreeSum.TernaryBank
