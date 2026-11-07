-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.displacement_ball_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:55:24.433319+00:00
-- url     : https://prove2.me/submissions/87b9f6ab-ef3b-4120-b53e-f19d22789b6a

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_SmallCap
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacement_distance_sq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set Metric
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {R ε : ℝ} (hR : 0 < R) (hε : 0 ≤ ε)
    (v : Sphere) :
    (fun s : Sphere => R • (s : Space)) ⁻¹' closedBall (R • (v : Space)) ε =
      cap v (1 - ε^2 / (2*R^2)) := by
  ext s
  change dist (R • (s : Space)) (R • (v : Space)) ≤ ε ↔
    1 - ε^2 / (2*R^2) ≤ inner ℝ (v : Space) (s : Space)
  rw [← sq_le_sq₀ dist_nonneg hε, displacement_distance_sq]
  have hden : 0 < 2*R^2 := by positivity
  rw [mul_comm (2*R^2), ← le_div_iff₀ hden]
  constructor <;> intro h <;> linarith
end QEC.Coding.ProbabilisticConstruction.SphericalCap
