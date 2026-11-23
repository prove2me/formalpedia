-- Prove2me | solution 1 for SumProduct.sub_mem_unitBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:22:27.816244+00:00
-- url     : https://prove2.me/submissions/1caf0ed8-7f49-42ec-b502-8a3b60ac7158

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
    (hy : y ∈ unitBox K a) (hz : z ∈ unitBox K b) : y - z ∈ unitBox K (a + b) := by
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨fun w => ?_, ?_⟩
  · rw [Pi.sub_apply, sub_eq_add_neg]
    calc |y w + -z w| ≤ |y w| + |(-z w)| := abs_add_le _ _
      _ = |y w| + |z w| := by rw [abs_neg]
      _ ≤ a + b := add_le_add (hy1 w) (hz1 w)
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [sub_eq_add_neg]
    calc |(∑ w, y w) + -(∑ w, z w)| ≤ |∑ w, y w| + |(-(∑ w, z w))| := abs_add_le _ _
      _ = |∑ w, y w| + |∑ w, z w| := by rw [abs_neg]
      _ ≤ a + b := add_le_add hy2 hz2
end SumProduct
