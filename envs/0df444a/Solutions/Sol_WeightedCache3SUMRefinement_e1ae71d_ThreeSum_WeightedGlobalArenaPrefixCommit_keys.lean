-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixCommit.keys
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:04:48.53523+00:00
-- url     : https://prove2.me/submissions/e4cf6eba-6ba9-4859-9a11-3f43ed62ec0a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixFinish
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixCommit
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixFinish
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixCommit
theorem _root_.solution {C : Config} {D : Data C} {R S rows newSpan : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {ξ ν : ℕ→ℤ}
    (H : Committed C rows newSpan ξ ν)
    (O : LightWeightedGlobalSeedScoreFull.Outputs C D R S raws words maps ξ) :
    Reads ν C.Bold C.nB D.newB ∧ Reads ν C.Cold C.nC D.newC ∧ Reads ν C.Oold C.nO D.newO :=by
  refine ⟨?_,?_,?_⟩
  · intro i hi; exact (H.2.1 i hi).trans (O.B i hi)
  · intro i hi; exact (H.2.2.1 i hi).trans (O.Cvalues i hi)
  · intro i hi; exact (H.2.2.2.1 i hi).trans (O.O i hi)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixCommit
