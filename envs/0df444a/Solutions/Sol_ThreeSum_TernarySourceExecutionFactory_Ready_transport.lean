-- Prove2me | solution 1 for ThreeSum.TernarySourceExecutionFactory.Ready.transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:27:04.0035+00:00
-- url     : https://prove2.me/submissions/9d00db89-b267-44ac-b4b2-b317474d4e46

import Definitions.Def_Submission_ThreeSum_LightTernarySourceCountHost
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySourceExecutionFactory
open Light LightSubsetAddress LightTernarySourceHost
namespace ThreeSum.TernarySourceExecutionFactory
namespace Ready
theorem _root_.solution {N : ℕ} {S : Setup} {lim : Limits} {d keep : ℕ}
    {μ ν : ℕ→ℤ} {weight : ℕ→ℤ} {enumeration : ℕ→TernaryJointType.TritWord N}
    (H : Ready S lim d μ weight enumeration) (hkeep : Kept μ ν keep)
    (hsrc : S.src+S.NL≤keep) (hweights : S.weightBase+S.NL≤keep)
    (hcodes : S.a+S.bank≤keep) (hpowers : S.powers+(S.W+1)≤keep) :
    Ready S lim d ν weight enumeration := by
  refine {H with hinput := ?_,hweightRead := ?_,hcodes := ?_,hpowers := ?_}
  · intro i hi
    exact (hkeep _ (by omega)).trans (H.hinput i hi)
  · intro i hi
    exact (hkeep _ (by omega)).trans (H.hweightRead i hi)
  · intro i hi
    exact (hkeep _ (by omega)).trans (H.hcodes i hi)
  · intro i hi
    exact (hkeep _ (by omega)).trans (H.hpowers i hi)
end Ready
end ThreeSum.TernarySourceExecutionFactory
