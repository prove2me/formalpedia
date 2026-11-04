-- Prove2me | solution 1 for ThreeSum.WeightedSourceCountExecutionFactory.Seed.transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:11:36.371902+00:00
-- url     : https://prove2.me/submissions/cc70a14c-2f53-4475-86fa-03eb5a7734df

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountExecutionFactory
import Definitions.Def_Submission_ThreeSum_TernarySourceWeightSeed
import Definitions.Def_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_transport
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_transport
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_transport


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType
namespace ThreeSum.WeightedSourceCountExecutionFactory
namespace Seed
theorem _root_.solution {N : ℕ} {S : Setup N} {lim : Limits} {d boundary keep : ℕ}
    {μ ν : ℕ→ℤ} {leftWeight rightWeight : ℕ→ℤ}
    (H : Seed S lim d boundary μ leftWeight rightWeight) (hkeep : Kept μ ν keep)
    (I : Immutable S keep) : Seed S lim d boundary ν leftWeight rightWeight := by
  exact {H with
    left := H.left.transport hkeep I.leftInput I.leftCodes I.leftPowers
    right := H.right.transport hkeep I.rightInput I.rightCodes I.rightPowers
    front := H.front.transport hkeep I.frontCodes I.frontRecords}
end Seed
end ThreeSum.WeightedSourceCountExecutionFactory
