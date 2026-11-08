-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.exists_grid_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:33:27.645407+00:00
-- url     : https://prove2.me/submissions/08774484-1145-4426-b477-0c377a8a3955

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_nearestGrid_dist
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (K : ℕ) (center p : Space) (hp : p ∈ Metric.closedBall center K) :
    ∃ g : Grid K, p ∈ Metric.closedBall (center+gridPoint K g) 1 := by
  have hn : ‖p-center‖ ≤ K := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hp
  refine ⟨nearestGrid K (p-center) hn, ?_⟩
  have h := nearestGrid_dist K (p-center) hn
  have he : p-(center+gridPoint K (nearestGrid K (p-center) hn)) =
      (p-center)-gridPoint K (nearestGrid K (p-center) hn) := by abel
  simpa only [Metric.mem_closedBall,dist_eq_norm,he] using h
end QEC.Coding.BDL26RandomPerturbation
