-- Prove2me | solution 1 for ThreeSum.TernaryCoverHighMoment.jointEvent_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:53:11.834135+00:00
-- url     : https://prove2.me/submissions/5deac8f3-8eca-4d60-be1e-cc1506123916

import Definitions.Def_Submission_ThreeSum_TernaryCoverTupleCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Definitions.Def_Submission_ThreeSum_TernaryCoverMoments
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverHighMoment
open Finset TernaryCoverRankFibers TernaryCoverTupleCount
open TernaryCoverRelations TernaryCoverUniformRank TernaryCoverMoments
open scoped BigOperators
variable {K E σ : Type*} [Field K] [Fintype E] [Fintype σ] [DecidableEq σ]
variable [Fintype K] [DecidableEq K]
namespace ThreeSum.TernaryCoverHighMoment
theorem _root_.solution (left right : E → σ → Fin 3) (a b : K) {k : ℕ} (es : Fin k → E) :
    jointEvent (rawEvents (K := K) left right a b) es =
      prescribedEvent (rows left right es) (flattenPairs k (fun _ => (a,b))) := by
  classical
  ext w
  simp only [jointEvent, rawEvents, prescribedEvent, mem_filter, mem_univ, true_and]
  constructor
  · intro h j
    obtain ⟨ab, rfl⟩ := finProdFinEquiv.surjective j
    obtain ⟨e,t⟩ := ab
    have ht : t = 0 ∨ t = 1 := by omega
    rcases ht with ht | ht
    · subst t
      simpa only [HashFamily.hashMap_apply, rows, flattenPairs_prod_zero, tupleColumn] using (h e).1
    · subst t
      simpa only [HashFamily.hashMap_apply, rows, flattenPairs_prod_one, tupleColumn] using (h e).2
  · intro h e
    constructor
    · simpa only [HashFamily.hashMap_apply, rows, flattenPairs_prod_zero, tupleColumn] using h (finProdFinEquiv (e,0))
    · simpa only [HashFamily.hashMap_apply, rows, flattenPairs_prod_one, tupleColumn] using h (finProdFinEquiv (e,1))
end ThreeSum.TernaryCoverHighMoment
