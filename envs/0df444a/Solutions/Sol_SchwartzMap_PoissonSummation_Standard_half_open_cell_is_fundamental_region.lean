-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.half_open_cell_is_fundamental_region
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/01cfc91d-3af9-4c5b-a080-568beaa356d9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_unit_cell_null_measurable
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_unique_integer_shift_into_half_open_cell

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
namespace SchwartzMap.PoissonSummation.Standard
theorem _root_.solution :
    MeasureTheory.IsAddFundamentalDomain (SchwartzMap.referenceIntegerLattice d)
      (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  refine MeasureTheory.IsAddFundamentalDomain.mk'
      (SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_null_measurable (d := d)) ?_
  intro x
  rcases SchwartzMap.PoissonSummation.Standard.unique_integer_shift_into_half_open_cell (d := d) x with
    ⟨n, hn, hn_unique⟩
  refine
    ⟨(⟨SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n,
        SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_mem_reference_lattice (d := d) n⟩), ?_, ?_⟩
  ·
    simpa [Submodule.vadd_def, vadd_eq_add, add_comm, add_left_comm, add_assoc] using! hn
  ·
    intro ℓ hℓ
    rcases
        SchwartzMap.PoissonSummation.Standard.reference_lattice_element_eq_integer_vector (d := d)
          (ℓ : (EuclideanSpace ℝ (Fin d))) ℓ.property with
      ⟨n', hn'⟩
    have : n' = n := hn_unique n' (by
      simpa [Submodule.vadd_def, vadd_eq_add, add_comm, add_left_comm, add_assoc, hn'] using! hℓ)
    apply Subtype.ext
    simp [hn', this]
end SchwartzMap.PoissonSummation.Standard
