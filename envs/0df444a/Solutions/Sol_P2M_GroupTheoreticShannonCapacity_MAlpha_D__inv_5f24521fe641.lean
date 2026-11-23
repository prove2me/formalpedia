-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_MAlpha_D__inv_5f24521fe641
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:26:47.046433+00:00
-- url     : https://prove2.me/submissions/b06fac99-1260-4b22-a047-f271deac95a2

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix
namespace GroupTheoreticShannonCapacity.MAlpha
theorem _root_.solution (n : ℕ) (β : ℝ) (hβ : β ≠ 0) :
    (Dα n β)⁻¹ = Dα n (β⁻¹) := by
  simp only [Dα]
  rw [Matrix.inv_diagonal]
  congr 1
  -- Show Ring.inverse (fun i => β^i) = fun i => β⁻¹^i
  have hu : IsUnit (fun i : Fin n => β ^ (i.val : ℕ)) := by
    rw [Pi.isUnit_iff]
    intro i
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hβ)
  have h := Ring.inverse_unit hu.unit
  simp only [IsUnit.unit_spec] at h
  rw [h]
  ext i
  simp only [Units.val_inv_eq_inv_val, Pi.inv_apply, IsUnit.unit_spec, inv_pow]
end GroupTheoreticShannonCapacity.MAlpha
