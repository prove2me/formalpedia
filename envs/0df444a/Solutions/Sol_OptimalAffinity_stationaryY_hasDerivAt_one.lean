-- Prove2me | solution 1 for OptimalAffinity.stationaryY_hasDerivAt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:49.461793+00:00
-- url     : https://prove2.me/submissions/1bb1007f-fe69-4b74-b668-c052378c39c7

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section
namespace OptimalAffinity
theorem _root_.solution :
    HasDerivAt stationaryY (3/2) 1 := by
  have ha : HasDerivAt (fun x : ℝ => 6*x^2 - 2) 12 1 := by
    have h := (((hasDerivAt_id (1 : ℝ)).pow 2).const_mul 6).sub_const 2
    simpa [id, show (6 : ℝ) * 2 = 12 by norm_num] using h
  have hd : HasDerivAt
      (fun x : ℝ => (6*x^2 - 2)^2 + 84*x) 180 1 := by
    have h := (ha.pow 2).add ((hasDerivAt_id (1 : ℝ)).const_mul 84)
    have h1 : HasDerivAt (fun x : ℝ => (6*x^2 - 2)^2 + 84*x) _ 1 :=
      h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp [Pi.add_apply, Pi.pow_apply])
    simpa [id, show (2 : ℝ) * (6 - 2) * 12 + 84 = 180 by norm_num] using h1
  have hs : HasDerivAt
      (fun x : ℝ => Real.sqrt ((6*x^2 - 2)^2 + 84*x)) 9 1 := by
    have h := hd.sqrt (by norm_num : (6*(1:ℝ)^2 - 2)^2 + 84*1 ≠ 0)
    simpa [show (180 : ℝ) / (2 * Real.sqrt ((6 - 2) ^ 2 + 84)) = 9 by norm_num] using h
  change HasDerivAt
    (fun x : ℝ => (6*x^2 - 2 + Real.sqrt ((6*x^2 - 2)^2 + 84*x)) / 14)
      (3/2) 1
  have h := (ha.add hs).div_const 14
  simpa [show ((12 : ℝ) + 9) / 14 = 3 / 2 by norm_num] using h
end OptimalAffinity
