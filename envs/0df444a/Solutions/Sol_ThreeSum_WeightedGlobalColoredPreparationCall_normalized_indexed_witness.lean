-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredPreparationCall.normalized_indexed_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:42:43.903266+00:00
-- url     : https://prove2.me/submissions/ac957b95-b828-451f-b4e3-aa7c3b429028

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPreparationCall
import Theorems.Thm_ThreeSum_WeightedGlobalColoredPreparationCall_indexed_witness
import Theorems.Thm_ThreeSum_ColorClassLists_witness_iff
import Theorems.Thm_ThreeSum_LightTernaryColorPrelude_witness_iff


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPreparationCall
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalColoredPreparationCall
theorem _root_.solution {n : ℕ}
    {p : Coloring.Parameter (LightColorParametersCosts.width n)} {x : Fin n→ℤ}
    {μ : ℕ→ℤ} {ab bb cb : ℕ} {A B C : List ℤ}
    (hA : LightTernaryColorPrelude.Normalized μ ab n (ColorClassLists.classList p x 0 1) A)
    (hB : LightTernaryColorPrelude.Normalized μ bb n (ColorClassLists.classList p x 1 1) B)
    (hC : LightTernaryColorPrelude.Normalized μ cb n (ColorClassLists.classList p x 2 (-1)) C) :
    (∃i<A.length,∃j<B.length,∃k<C.length,C.getD k 0=A.getD i 0+B.getD j 0)↔
      ColorClassLists.witness p x :=
  (indexed_witness A B C).trans (LightTernaryColorPrelude.witness_iff hA hB hC)
end ThreeSum.WeightedGlobalColoredPreparationCall
