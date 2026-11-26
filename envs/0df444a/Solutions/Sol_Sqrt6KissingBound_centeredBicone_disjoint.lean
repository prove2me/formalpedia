-- Prove2me | solution 1 for Sqrt6KissingBound.centeredBicone_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:24:51.268068+00:00
-- url     : https://prove2.me/submissions/57825492-58d3-4a29-8cbd-c6c2c3f83b61

import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Theorems.Thm_Sqrt6KissingBound_centeredBicone_subset_cone_ball
import Theorems.Thm_Sqrt6KissingBound_strictCone_disjoint


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution {k : ℕ}
    {x z : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1)
    (hxz : inner ℝ x z ≤ (1 : ℝ) / 2) :
    Disjoint (centeredBicone k x) (centeredBicone k z) := by
  exact (strictCone_disjoint hx hz hxz).mono
    (fun _ hy => (centeredBicone_subset_cone_ball hx hy).1)
    (fun _ hy => (centeredBicone_subset_cone_ball hz hy).1)
end Sqrt6KissingBound
