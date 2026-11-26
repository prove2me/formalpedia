-- Prove2me | solution 1 for Sqrt6KissingBound.centeredBicone_subset_unitBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:24:50.610361+00:00
-- url     : https://prove2.me/submissions/3a8b5670-f69d-4d88-b70e-1dd35df03290

import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Theorems.Thm_Sqrt6KissingBound_centeredBicone_subset_cone_ball

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution {k : ℕ}
    {x : EuclideanSpace ℝ (Fin (k + 2))} (hx : ‖x‖ = 1) :
    centeredBicone k x ⊆ ball 0 1 :=
  fun _ hy => (centeredBicone_subset_cone_ball hx hy).2
end Sqrt6KissingBound
