-- Prove2me | solution 1 for ThreeSum.LightWeightedFrozenQuery.count_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:28:43.613877+00:00
-- url     : https://prove2.me/submissions/5d631c45-ebc0-439d-a752-73d58fef0959

import Definitions.Def_Submission_Weighted_FrozenMain
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_Weighted_FrozenPhysical
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_stageValue_count
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedFrozenQueryCost (cacheCost)
open ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedFrozenQuery
theorem _root_.solution {N a b pMain d time : ℕ} (args : List ℤ) (μ : ℕ→ℤ)
    (f g : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b)
    (hquery : Meets lim P pMain d args μ time (fun v μ' =>
      v=stageValue N (fun R => ThreeSum.TernaryEuler.binomialZeta
        (fun A => ThreeSum.TernaryConvolution.factorial A*f A) R *
        ThreeSum.TernaryEuler.binomialZeta (fun B => ThreeSum.TernaryConvolution.factorial B*g B) R) Q ∧ μ'=μ)) :
    Meets lim P pMain d args μ time (fun v μ' =>
      v=ThreeSum.TernaryConvolution.factorial Q*ThreeSum.TernaryConvolution.convolution f g Q ∧ μ'=μ) := by
  exact hquery.mono le_rfl (fun v μ' hv =>
    ⟨hv.1.trans (stageValue_count f g hf hg Q hQ),hv.2⟩)
end ThreeSum.LightWeightedFrozenQuery
