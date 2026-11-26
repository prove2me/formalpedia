-- Prove2me | solution 1 for Sqrt6KissingBound.centeredBody_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:21:30.368445+00:00
-- url     : https://prove2.me/submissions/b41aec61-ae3f-488c-be6c-dee0680f93fc

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Theorems.Thm_Sqrt6KissingBound_centeredBody_subset_cone_ball
import Theorems.Thm_Sqrt6KissingBound_strictCone_disjoint


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))}
    (hS : S ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1)
    {x z : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1)
    (hxz : inner ℝ x z ≤ (1 : ℝ) / 2) :
    Disjoint (centeredBody k S x) (centeredBody k S z) := by
  exact (strictCone_disjoint hx hz hxz).mono
    (fun _ hy => (centeredBody_subset_cone_ball hS hx hy).1)
    (fun _ hy => (centeredBody_subset_cone_ball hS hz hy).1)
end Sqrt6KissingBound
