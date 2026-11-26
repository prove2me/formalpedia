-- Prove2me | solution 1 for Sqrt6KissingBound.centeredBody_subset_unitBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:14:23.391626+00:00
-- url     : https://prove2.me/submissions/8081bee9-b03c-4d64-b2ca-06f8aeecb15b

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Theorems.Thm_Sqrt6KissingBound_centeredBody_subset_cone_ball

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))}
    (hS : S ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1)
    {x : EuclideanSpace ℝ (Fin (k + 2))} (hx : ‖x‖ = 1) :
    centeredBody k S x ⊆ ball 0 1 :=
  fun _ hy => (centeredBody_subset_cone_ball hS hx hy).2
end Sqrt6KissingBound
