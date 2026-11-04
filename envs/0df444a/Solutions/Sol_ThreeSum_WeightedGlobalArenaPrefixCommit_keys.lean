-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixCommit.keys
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:07:19.849206+00:00
-- url     : https://prove2.me/submissions/422346e2-0b43-469a-ad48-2bfb95903eed

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixCommit
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixFinish
namespace ThreeSum.WeightedGlobalArenaPrefixCommit
theorem _root_.solution {C : Config} {D : Data C} {R S rows newSpan : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {ξ ν : ℕ→ℤ}
    (H : Committed C rows newSpan ξ ν)
    (O : LightWeightedGlobalSeedScoreFull.Outputs C D R S raws words maps ξ) :
    Reads ν C.Bold C.nB D.newB ∧ Reads ν C.Cold C.nC D.newC ∧ Reads ν C.Oold C.nO D.newO :=by
  refine ⟨?_,?_,?_⟩
  · intro i hi; exact (H.2.1 i hi).trans (O.B i hi)
  · intro i hi; exact (H.2.2.1 i hi).trans (O.Cvalues i hi)
  · intro i hi; exact (H.2.2.2.1 i hi).trans (O.O i hi)
end ThreeSum.WeightedGlobalArenaPrefixCommit
