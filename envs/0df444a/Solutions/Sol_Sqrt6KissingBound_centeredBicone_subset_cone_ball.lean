-- Prove2me | solution 1 for Sqrt6KissingBound.centeredBicone_subset_cone_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:23:37.594273+00:00
-- url     : https://prove2.me/submissions/33096408-360e-4adf-a704-38ae4afdadd0

import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Theorems.Thm_Sqrt6KissingBound_axisTo_standardAxis
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_preimage_strictCone_linearIsometryEquiv
import Theorems.Thm_Sqrt6KissingBound_standardBicone_subset
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution {k : ℕ}
    {x : EuclideanSpace ℝ (Fin (k + 2))} (hx : ‖x‖ = 1) :
    centeredBicone k x ⊆ strictCone x ∩ ball 0 1 := by
  intro y hy
  let A := axisTo k x
  let z := A.symm y
  have hz : z ∈ standardBicone k := hy
  have hzsub := standardBicone_subset k hz
  constructor
  · have hzpre : z ∈ A ⁻¹' strictCone x := by
      rw [preimage_strictCone_linearIsometryEquiv A
        (axisTo_standardAxis hx)]
      exact hzsub.1
    simpa [A, z] using hzpre
  · rw [mem_ball, dist_zero_right]
    have hzball : ‖z‖ < 1 := by
      simpa [mem_ball, dist_zero_right] using hzsub.2
    simpa [A, z] using hzball
end Sqrt6KissingBound
