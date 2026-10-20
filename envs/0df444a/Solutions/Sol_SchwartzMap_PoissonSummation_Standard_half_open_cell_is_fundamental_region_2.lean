-- Prove2me | solution 2 for SchwartzMap.PoissonSummation.Standard.half_open_cell_is_fundamental_region
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:04:48.259396+00:00
-- url     : https://prove2.me/submissions/bf7e4215-2147-4d5d-ba45-6112dc829d42

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators
open MeasureTheory
open SchwartzMap
variable {d : ℕ}
open SchwartzMap.PoissonSummation SchwartzMap.PoissonSummation.Standard
open UnitAddTorus
theorem h47b_shift (x : (EuclideanSpace ℝ (Fin d))) :
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

theorem solution :
    MeasureTheory.IsAddFundamentalDomain (SchwartzMap.referenceIntegerLattice d)
      (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  apply MeasureTheory.IsAddFundamentalDomain.mk'
  · apply MeasurableSet.nullMeasurableSet
    show MeasurableSet {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, x i ∈ Set.Ioc (0 : ℝ) 1}
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_Ioc.preimage (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin d) => x i)
  · intro x
    obtain ⟨n, hn, huniq⟩ := h47b_shift x
    refine ⟨⟨embeddedIntegerVector n, embedded_integer_vector_mem_reference_lattice n⟩, ?_, ?_⟩
    · simp only [Submodule.vadd_def, vadd_eq_add]
      rwa [add_comm]
    · intro g hg
      obtain ⟨m, hm⟩ := reference_lattice_element_eq_integer_vector (g : EuclideanSpace ℝ (Fin d)) g.2
      simp only [Submodule.vadd_def, vadd_eq_add] at hg
      rw [hm, add_comm] at hg
      have := huniq m hg
      apply Subtype.ext
      rw [hm, this]

