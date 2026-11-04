-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixCommit.outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:54:41.044515+00:00
-- url     : https://prove2.me/submissions/52fab1ba-e110-4cfc-82ce-28f8b0e7508c

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
theorem _root_.solution {C : Config} {rows newSpan : ℕ} {ξ ν : ℕ→ℤ}
    (H : Committed C rows newSpan ξ ν) (x : ℕ)
    (hk : x<C.Bold ∨ C.Oold+C.nO≤x) (hs : x<C.catalog ∨ C.catalog+rows*C.J≤x) :
    ν x=ξ x :=H.2.2.2.2.2 x hk hs
end ThreeSum.WeightedGlobalArenaPrefixCommit
