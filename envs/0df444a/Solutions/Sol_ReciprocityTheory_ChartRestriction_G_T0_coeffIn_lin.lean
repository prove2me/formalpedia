-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.coeffIn_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:18:48.153785+00:00
-- url     : https://prove2.me/submissions/8d7b5351-82a6-40b7-92d7-9536593efb72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SumLeSqrtCardMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B] {D N : ℕ}
variable (W : Submodule R B)
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (w : Fin (N + 1) → B) (hw : ∀ j, w j ∈ W) (i : Fin (D + 2)) :
    CoeffIn W 1 (∑ j, X (i, j) * C (w j) : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) := fun β => by
  rw [coeff_sum, pow_one]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [mul_comm, coeff_C_mul, coeff_X']
  split_ifs
  · rw [mul_one]
    exact hw j
  · rw [mul_zero]
    exact zero_mem _
end ReciprocityTheory.ChartRestriction.G.T0
