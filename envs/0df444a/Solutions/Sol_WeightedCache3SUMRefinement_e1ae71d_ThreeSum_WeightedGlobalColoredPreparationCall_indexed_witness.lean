-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationCall.indexed_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:59:46.35332+00:00
-- url     : https://prove2.me/submissions/57f275bd-ab48-49ee-9edb-bfd7dc1e0ac7

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredSolverNeed
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPreparationCall

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationCall
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationCall
theorem _root_.solution (A B C : List ℤ) :
    (∃i<A.length,∃j<B.length,∃k<C.length,C.getD k 0=A.getD i 0+B.getD j 0)↔
      LightTernaryColorPrelude.witness A B C := by
  constructor
  · rintro ⟨i,hi,j,hj,k,hk,he⟩
    refine ⟨A.getD i 0,?_,B.getD j 0,?_,C.getD k 0,?_,by omega⟩
    · rw [List.getD_eq_getElem A 0 hi];exact List.getElem_mem hi
    · rw [List.getD_eq_getElem B 0 hj];exact List.getElem_mem hj
    · rw [List.getD_eq_getElem C 0 hk];exact List.getElem_mem hk
  · rintro ⟨a,ha,b,hb,c,hc,he⟩
    rcases List.mem_iff_getElem.mp ha with ⟨i,hi,ha⟩
    rcases List.mem_iff_getElem.mp hb with ⟨j,hj,hb⟩
    rcases List.mem_iff_getElem.mp hc with ⟨k,hk,hc⟩
    refine ⟨i,hi,j,hj,k,hk,?_⟩
    rw [List.getD_eq_getElem A 0 hi,List.getD_eq_getElem B 0 hj,List.getD_eq_getElem C 0 hk]
    omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationCall
