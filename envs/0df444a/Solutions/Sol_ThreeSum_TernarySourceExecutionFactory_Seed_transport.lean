-- Prove2me | solution 1 for ThreeSum.TernarySourceExecutionFactory.Seed.transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:50:44.448194+00:00
-- url     : https://prove2.me/submissions/36c7e0d0-f03c-4d8a-8fa9-4ec00012b8ad

import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_Submission_ThreeSum_TernarySourceWeightSeed
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySourceExecutionFactory
open Light LightSubsetAddress LightTernarySourceHost
namespace ThreeSum.TernarySourceExecutionFactory
namespace Seed
theorem _root_.solution {N : ℕ} {S : Setup} {lim : Limits} {d keep : ℕ}
    {μ ν : ℕ→ℤ} {weight : ℕ→ℤ} {enumeration : ℕ→TernaryJointType.TritWord N}
    (H : Seed S lim d μ weight enumeration) (hkeep : Kept μ ν keep)
    (hsrc : S.src+S.NL≤keep) (hcodes : S.a+S.bank≤keep)
    (hpowers : S.powers+(S.W+1)≤keep) : Seed S lim d ν weight enumeration := by
  refine {H with hinput := ?_,hcodes := ?_,hpowers := ?_}
  · intro i hi
    exact (hkeep _ (by omega)).trans (H.hinput i hi)
  · intro i hi
    exact (hkeep _ (by omega)).trans (H.hcodes i hi)
  · intro i hi
    exact (hkeep _ (by omega)).trans (H.hpowers i hi)
end Seed
end ThreeSum.TernarySourceExecutionFactory
