-- Prove2me | solution 1 for ThreeSum.BandRawA.sum_ownerProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:00:53.959726+00:00
-- url     : https://prove2.me/submissions/6dd4f7b9-fb4b-49eb-8072-7b1e8e615ea9

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Theorems.Thm_ThreeSum_BandRawA_sum_aIndices
import Theorems.Thm_ThreeSum_BandRawA_sum_bandPositions

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) (s : ℕ) :
    (∑ t ∈ ownerProduct nA nB nC g rs s, F t)=
      ∑ i ∈ range (row nA g s (rs.getD s default)).length,
        ∑ j ∈ range (bandLength nB g (rs.getD s default).b),
          ∑ k ∈ range (bandLength nC g (rs.getD s default).c),
            F (count nA g rs s+i,
              BandPartition.start g (rs.getD s default).b+j,
              BandPartition.start g (rs.getD s default).c+k) := by
  rw [ownerProduct,sum_product,sum_aIndices]
  apply sum_congr rfl
  intro i hi
  rw [sum_product,sum_bandPositions]
  apply sum_congr rfl
  intro j hj
  exact sum_bandPositions _ _ _ _
end ThreeSum.BandRawA
