-- Prove2me | solution 2 for SchwartzMap.PoissonSummation.Standard.unique_integer_shift_into_half_open_cell
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:03:45.227893+00:00
-- url     : https://prove2.me/submissions/68005926-0721-47e9-a556-b2c332b9b609

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


theorem solution (x : (EuclideanSpace ℝ (Fin d))) :
    ∃! n : Fin d → ℤ, x + SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n ∈
      halfOpenUnitCell (d := d) := by
  refine ⟨fun i => ⌊1 - x i⌋, ?_, ?_⟩
  · intro i
    simp only [PiLp.add_apply, embedded_integer_vector_coordinate, Set.mem_Ioc]
    have h1 := Int.floor_le (1 - x i)
    have h2 := Int.lt_floor_add_one (1 - x i)
    constructor <;> linarith
  · intro m hm
    funext i
    have h := hm i
    simp only [PiLp.add_apply, embedded_integer_vector_coordinate, Set.mem_Ioc] at h
    rw [eq_comm, Int.floor_eq_iff]
    constructor <;> linarith [h.1, h.2]

