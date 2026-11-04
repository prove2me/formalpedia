-- Prove2me | solution 1 for ThreeSum.LightTernaryCountFrontend.weighted_count_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:12:48.176115+00:00
-- url     : https://prove2.me/submissions/cb3eb333-9b9a-49ad-b1c9-0bae6c58c826

import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankResources
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedRows
import Definitions.Def_Submission_ThreeSum_LightTernaryCountFrontend
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_stageValue_count


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryCountFrontend
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryWantedRowDispatch ThreeSum.LightTernaryPreparedState
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000
namespace ThreeSum.LightTernaryCountFrontend
theorem _root_.solution {lim : Limits} {P : Program}
    {N a b pMain d t count dst keep : ℕ} (argv : List ℤ) (μ : ℕ→ℤ)
    (f g : ℕ→TritWord N→ℤ) (group : ℕ→ℕ) (Q : ℕ→TritWord N)
    (hf : ∀ j<count, ∀ A, f (group j) A≠0 → rank A=a)
    (hg : ∀ j<count, ∀ B, g (group j) B≠0 → rank B=b)
    (hQ : ∀ j<count, rank (Q j)=a+b)
    (h : Meets lim P pMain d argv μ t (fun _ ν => Kept μ ν keep ∧ ∀ j<count,
      ν (dst+j)=LightTernaryWantedRows.score
        (fun k A => ThreeSum.TernaryConvolution.factorial A*f k A)
        (fun k B => ThreeSum.TernaryConvolution.factorial B*g k B) group Q j)) :
    Meets lim P pMain d argv μ t (fun _ ν => Kept μ ν keep ∧ ∀ j<count,
      ν (dst+j)=ThreeSum.TernaryConvolution.factorial (Q j)*
        ThreeSum.TernaryConvolution.convolution (f (group j)) (g (group j)) (Q j)) := by
  apply h.mono le_rfl
  intro r ν hv
  refine ⟨hv.1,?_⟩
  intro j hj
  rw [hv.2 j hj]
  exact LightTernaryFrozenQuery.stageValue_count (f (group j)) (g (group j)) (hf j hj) (hg j hj) (Q j) (hQ j hj)
end ThreeSum.LightTernaryCountFrontend
