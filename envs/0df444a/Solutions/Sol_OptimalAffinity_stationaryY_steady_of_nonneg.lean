-- Prove2me | solution 1 for OptimalAffinity.stationaryY_steady_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:50.760133+00:00
-- url     : https://prove2.me/submissions/42712312-b14f-44da-82e0-285173226667

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge
public import Theorems.Thm_OptimalAffinity_oa2x2_ySteady_iff


set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section
namespace OptimalAffinity
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) :
    YSteady oa2x2 x (stationaryY x) := by
  have hd : 0 ≤ (6*x^2 - 2)^2 + 84*x := by
    positivity
  have hs := Real.sq_sqrt hd
  have hid :
      28 * (7 * (stationaryY x)^2 -
        (6*x^2 - 2) * stationaryY x - 3*x) =
      (Real.sqrt ((6*x^2 - 2)^2 + 84*x))^2 -
        (6*x^2 - 2)^2 - 84*x := by
    unfold stationaryY
    ring
  rw [hs] at hid
  apply (oa2x2_ySteady_iff x (stationaryY x)).mpr
  nlinarith
end OptimalAffinity
