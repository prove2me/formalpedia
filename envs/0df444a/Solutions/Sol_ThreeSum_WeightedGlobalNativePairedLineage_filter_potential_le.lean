-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativePairedLineage.filter_potential_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:28:39.853556+00:00
-- url     : https://prove2.me/submissions/f4864723-1db1-4818-8164-168e7589cfbf

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryPairedContraction
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairedLineage
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativePairedLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalNativePairedLineage
theorem _root_.solution {P : Type*} [Fintype P] {d Λ : ℕ}
    (A : P→Matrix (Fin d) (Fin Λ) ℤ) (keep : P→Prop) [DecidablePred keep] :
    (∑ q : {q : P // keep q}, minorWeight (A q.val))≤potential A := by
  classical
  unfold potential
  calc
    _ = ∑ q∈(univ : Finset {q : P // keep q}).image Subtype.val, minorWeight (A q) := by
      rw [sum_image]
      exact fun a ha b hb h => Subtype.ext h
    _ ≤ _ := sum_le_sum_of_subset (subset_univ _)
end ThreeSum.WeightedGlobalNativePairedLineage
