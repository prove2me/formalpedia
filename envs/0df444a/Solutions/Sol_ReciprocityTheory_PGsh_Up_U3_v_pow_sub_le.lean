-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.v_pow_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:17.395904+00:00
-- url     : https://prove2.me/submissions/e567134e-aa48-4f66-8c12-ea06aaeb57be

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution {r s : C} (hr : v r ≤ 1) (hs : v s ≤ 1) (i : ℕ) :
    v (r ^ i - s ^ i) ≤ v (r - s) := by
  rw [← geom_sum₂_mul, map_mul]
  have hS : v (∑ j ∈ range i, r ^ j * s ^ (i - 1 - j)) ≤ 1 := by
    apply v.map_sum_le
    intro j _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one₀ (pow_le_one₀ zero_le' hr) zero_le' (pow_le_one₀ zero_le' hs)
  calc _ ≤ 1 * v (r - s) := mul_le_mul_of_nonneg_right hS zero_le'
    _ = _ := one_mul _
end ReciprocityTheory.PGsh.Up.U3
