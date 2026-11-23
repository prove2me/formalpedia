-- Prove2me | solution 1 for SumProduct.add_mem_unitBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:50:00.870689+00:00
-- url     : https://prove2.me/submissions/03cc7282-237d-42a7-b123-2faf06f1c70e

import Mathlib
import Definitions.Def_SumProduct_Boxes
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {y z : logSpace K} {a b : ℝ}
    (hy : y ∈ unitBox K a) (hz : z ∈ unitBox K b) : y + z ∈ unitBox K (a + b) := by
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨fun w => ?_, ?_⟩
  · calc |(y + z) w| = |y w + z w| := by rw [Pi.add_apply]
      _ ≤ |y w| + |z w| := abs_add_le _ _
      _ ≤ a + b := add_le_add (hy1 w) (hz1 w)
  · simp only [Pi.add_apply, Finset.sum_add_distrib]
    calc |(∑ w, y w) + ∑ w, z w| ≤ |∑ w, y w| + |∑ w, z w| := abs_add_le _ _
      _ ≤ a + b := add_le_add hy2 hz2
end SumProduct
