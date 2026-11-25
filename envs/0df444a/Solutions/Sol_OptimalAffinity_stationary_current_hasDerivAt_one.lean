-- Prove2me | solution 1 for OptimalAffinity.stationary_current_hasDerivAt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:05:39.574153+00:00
-- url     : https://prove2.me/submissions/171085ce-19bf-4954-b2ae-6bdd5d943ef9

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge
public import Theorems.Thm_OptimalAffinity_stationaryY_hasDerivAt_one
public import Theorems.Thm_OptimalAffinity_oa2x2_current_formula


set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section
namespace OptimalAffinity
theorem _root_.solution :
    HasDerivAt
      (fun x => productionCurrent oa2x2 x (stationaryY x)) 0 1 := by
  have h : HasDerivAt (fun x : ℝ => 3*x - 2*stationaryY x) 0 1 := by
    have h' := ((hasDerivAt_id (1 : ℝ)).const_mul 3).sub
      (stationaryY_hasDerivAt_one.const_mul 2)
    have h1 : HasDerivAt (fun x : ℝ => 3*x - 2*stationaryY x) _ 1 :=
      h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp [Pi.sub_apply])
    simpa [id, show (3 : ℝ) - 2 * (3 / 2) = 0 by norm_num] using h1
  simpa only [oa2x2_current_formula] using h
end OptimalAffinity
