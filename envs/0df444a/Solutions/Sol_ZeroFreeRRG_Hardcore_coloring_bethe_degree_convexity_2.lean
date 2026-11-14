-- Prove2me | solution 2 for ZeroFreeRRG.Hardcore.coloring_bethe_degree_convexity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:05:31.162081+00:00
-- url     : https://prove2.me/submissions/fa80f785-3ebd-46c7-bbb0-2497439bc0d7

import Theorems.Thm_ZeroFreeRRG_Hardcore_convex_interpolation_of_monotone_increments
import Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_vertex_entropy_increment
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore

theorem solution (q : ℕ) (hq : 3 ≤ q)
    (ν : ProbabilityMeasure ((.potts q : Model).Spin → ℝ)) (hν : ν ∈ cavityLaws (.potts q) 0) :
    ConvexOn ℝ (Set.Ici 0) (fun s => betheR (.potts q) 0 s ν) := by
  let v : ℕ → ℝ := fun k => betheK (.potts q) 0 k ν
  have hv : ∀ n, v (n+1)-v n ≤ v (n+2)-v (n+1) := by
    intro n
    have h := coloring_vertex_entropy_increment q hq ν hν n
    dsimp [v,betheK] at *
    push_cast at *
    linarith
  have hh := convex_interpolation_of_monotone_increments v hv
  convert hh using 1
  funext s
  dsimp [betheR,v]
