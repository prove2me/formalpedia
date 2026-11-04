-- Prove2me | solution 1 for ThreeSum.LightWeightedWantedQuery.weighted_count_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:21:43.387588+00:00
-- url     : https://prove2.me/submissions/7a75baf4-a2d9-4721-a28f-5b0ce9cfb02e

import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_FrozenPhysical
import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_WantedQuery
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_stageValue_count


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedWantedQuery
theorem _root_.solution {N a b pMain d t : ℕ} (argv : List ℤ) (μ : ℕ→ℤ)
    (f g : TritWord N→ℤ) (Q : TritWord N) (keep : ℕ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (hQ : rank Q=a+b)
    (hquery : Meets lim P pMain d argv μ t (fun v ν =>
      v=stageValue N (H (fun A => ThreeSum.TernaryConvolution.factorial A*f A)
        (fun B => ThreeSum.TernaryConvolution.factorial B*g B)) Q ∧ Kept μ ν keep)) :
    Meets lim P pMain d argv μ t (fun v ν =>
      v=ThreeSum.TernaryConvolution.factorial Q*ThreeSum.TernaryConvolution.convolution f g Q ∧
        Kept μ ν keep) := by
  apply hquery.mono le_rfl
  intro v ν hv
  refine ⟨hv.1.trans ?_,hv.2⟩
  exact LightWeightedFrozenQuery.stageValue_count f g hf hg Q hQ
end ThreeSum.LightWeightedWantedQuery
