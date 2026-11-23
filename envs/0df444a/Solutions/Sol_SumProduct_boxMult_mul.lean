-- Prove2me | solution 1 for SumProduct.boxMult_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:49:04.43035+00:00
-- url     : https://prove2.me/submissions/bc8d5200-f328-41ac-9209-4392a518bc28

import Mathlib
import Definitions.Def_SumProduct_Boxes
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {Y Y' : ℝ} {u v : (𝓞 K)ˣ}
    (hu : u ∈ boxMult K Y) (hv : v ∈ boxMult K Y') : u * v ∈ boxMult K (Y + Y') := by
  rw [mem_boxMult] at hu hv ⊢
  intro w
  have hu0 : w ((u : 𝓞 K) : K) ≠ 0 :=
    ne_of_gt (NumberField.InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero u))
  have hv0 : w ((v : 𝓞 K) : K) ≠ 0 :=
    ne_of_gt (NumberField.InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero v))
  have he : ((↑(u * v) : 𝓞 K) : K) = ((u : 𝓞 K) : K) * ((v : 𝓞 K) : K) := by push_cast; ring
  rw [he, map_mul, Real.log_mul hu0 hv0]
  calc |Real.log (w ((u : 𝓞 K) : K)) + Real.log (w ((v : 𝓞 K) : K))|
      ≤ |Real.log (w ((u : 𝓞 K) : K))| + |Real.log (w ((v : 𝓞 K) : K))| := abs_add_le _ _
    _ ≤ Y + Y' := add_le_add (hu w) (hv w)
end SumProduct
