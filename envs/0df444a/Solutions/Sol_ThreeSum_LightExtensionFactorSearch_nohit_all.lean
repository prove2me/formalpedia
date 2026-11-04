-- Prove2me | solution 1 for ThreeSum.LightExtensionFactorSearch.nohit_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:29.891541+00:00
-- url     : https://prove2.me/submissions/45efa67a-f366-469c-97ed-f7defdede64f

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Theorems.Thm_ThreeSum_LightPairSearch_first_pair_spec


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionFactorSearch
open Light LightExtensionFactorPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
attribute [local instance] ThreeSum.LightExtensionFactorSearch._p2m_local_instance_9c16afeb32_9
namespace ThreeSum.LightExtensionFactorSearch
theorem _root_.solution (C : Layout) (f : ℕ → ℕ) (q : ℕ) (hq : 0<q)
    (hp : 1≤C.p) (he : C.degree≤C.dim) (hcodes : C.p^C.dim≤q) :
    LightPairSearch.first (LightPairSearch.goodCode q (good C f)) (q*q)=0 ↔
      ∀ u v, ¬good C f u v := by
  rw [(LightPairSearch.first_pair_spec q hq (good C f)).1]
  constructor
  · intro h u v hg
    have hu : u<q := hg.1.trans_le ((Nat.pow_le_pow_right hp he).trans hcodes)
    have hv : v<q := hg.2.1.trans_le ((Nat.pow_le_pow_right hp (Nat.sub_le _ _)).trans hcodes)
    exact h u hu v hv hg
  · intro h u hu v hv
    exact h u v
end ThreeSum.LightExtensionFactorSearch
