-- Prove2me | solution 1 for Sqrt6KissingBound.centeredBody_subset_cone_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:13:24.589141+00:00
-- url     : https://prove2.me/submissions/f3a43944-c0f1-45c1-9699-2f67b97457fd

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Theorems.Thm_Sqrt6KissingBound_axisTo_standardAxis
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_preimage_strictCone_linearIsometryEquiv
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))}
    (hS : S ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1)
    {x : EuclideanSpace ℝ (Fin (k + 2))} (hx : ‖x‖ = 1) :
    centeredBody k S x ⊆ strictCone x ∩ ball 0 1 := by
  intro y hy
  let A := axisTo k x
  let z := A.symm y
  have hz : z ∈ S := hy
  have hzsub := hS hz
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
