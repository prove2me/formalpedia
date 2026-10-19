-- Prove2me | solution 1 for SchwartzMap.latticePoissonSummationFormula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/2465fc09-d3a6-4dec-9d83-e3f26170aac6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_integer_lattice_poisson_identity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
noncomputable section
open scoped BigOperators FourierTransform
open SchwartzMap
omit [Fact (0 < d)]
namespace SchwartzMap
theorem _root_.solution (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
  (v : EuclideanSpace ℝ (Fin d)) : ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
  ∑' m : polarIntegerLattice (d := d) Λ, (𝓕 ⇑f m) *
    Complex.exp (2 * Real.pi * Complex.I * ⟪v, m⟫_[ℝ]) := by
  simpa using! (SchwartzMap.integer_lattice_poisson_identity (d := d) (L := Λ) f v)
end SchwartzMap
