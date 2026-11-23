-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.eq_one_of_le_one_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:20.093326+00:00
-- url     : https://prove2.me/submissions/40df76d9-f5d6-4f73-a967-6e5979043e4c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution {a b : NNReal} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) :
    a = 1 := by
  have h1 := mul_le_of_le_one_right (zero_le : (0 : NNReal) ≤ a) hb
  rw [h] at h1
  exact le_antisymm ha h1
end ReciprocityTheory.PGsh.L2
