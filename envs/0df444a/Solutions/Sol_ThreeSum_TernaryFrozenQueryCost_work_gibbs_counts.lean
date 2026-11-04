-- Prove2me | solution 1 for ThreeSum.TernaryFrozenQueryCost.work_gibbs_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:28.157047+00:00
-- url     : https://prove2.me/submissions/c4d22692-b4ab-4f04-ab3e-baac0bea4b6d

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_work_le_capWord_card
import Theorems.Thm_ThreeSum_TernaryBank_nearWords_card_gibbs_counts


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryFrozenQueryCost
theorem _root_.solution {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : TritWord N) (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (work T coords R : ℝ)*z^(rank R+1-T) ≤
      (coords.length+1)*(1+z)^digitCount (capWord coords R) 1 *
        (1+z+z^2)^digitCount (capWord coords R) 2 := by
  have hw : (work T coords R : ℝ)≤
      (coords.length+1)*(nearWords (capWord coords R) (rank R+1-T)).card := by
    exact_mod_cast work_le_capWord_card T coords hcoords R
  have hg := nearWords_card_gibbs_counts (capWord coords R) (rank R+1-T) z hz hz1
  calc
    (work T coords R : ℝ)*z^(rank R+1-T) ≤
        ((coords.length+1)*(nearWords (capWord coords R) (rank R+1-T)).card)*z^(rank R+1-T) :=
      mul_le_mul_of_nonneg_right hw (pow_nonneg hz _)
    _ = (coords.length+1)*((nearWords (capWord coords R) (rank R+1-T)).card*z^(rank R+1-T)) := by ring
    _ ≤ (coords.length+1)*((1+z)^digitCount (capWord coords R) 1 *
        (1+z+z^2)^digitCount (capWord coords R) 2) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = (coords.length+1)*(1+z)^digitCount (capWord coords R) 1 *
        (1+z+z^2)^digitCount (capWord coords R) 2 := by ring
end ThreeSum.TernaryFrozenQueryCost
