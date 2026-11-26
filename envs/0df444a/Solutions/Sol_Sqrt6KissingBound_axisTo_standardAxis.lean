-- Prove2me | solution 1 for Sqrt6KissingBound.axisTo_standardAxis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:12:00.264585+00:00
-- url     : https://prove2.me/submissions/88fc3abe-ae2e-44bd-a53e-518d33214bec

import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution {k : ℕ} {x : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : ‖x‖ = 1) : axisTo k x (standardAxis (k + 1)) = x := by
  exact Submodule.reflection_sub (by rw [norm_standardAxis, hx])
end Sqrt6KissingBound
