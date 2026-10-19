-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.unique_integer_shift_into_half_open_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/1b89e000-d0c3-496f-ad43-7c3d6fecca9a

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators
open MeasureTheory
open SchwartzMap
open TopologicalSpace MeasureTheory
variable {d : ℕ}
open SchwartzMap.PoissonSummation SchwartzMap.PoissonSummation.Standard
open UnitAddTorus
namespace SchwartzMap.PoissonSummation.Standard
theorem _root_.solution (x : (EuclideanSpace ℝ (Fin d))) :
    ∃! n : Fin d → ℤ, x + SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n ∈
      halfOpenUnitCell (d := d) := by
  have hxcoord :
      ∀ i : Fin d, ∃! m : ℤ, (x i : ℝ) + m • (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i
    simpa [one_smul, add_assoc] using!
      (existsUnique_add_zsmul_mem_Ioc (G := ℝ) (ha := zero_lt_one) (b := (x i : ℝ))
        (c := (0 : ℝ)))
  choose n hn hn_unique using hxcoord
  refine ⟨n, ?_, ?_⟩
  ·
    intro i
    simpa [SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_coordinate, halfOpenUnitCell, zsmul_one] using! hn i
  ·
    intro n' hn'
    funext i
    have hcoords : ∀ i : Fin d,
        (x + SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n') i ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [halfOpenUnitCell] using! hn'
    exact hn_unique i (n' i) (by
      simpa [SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_coordinate, zsmul_one] using! hcoords i)
end SchwartzMap.PoissonSummation.Standard
