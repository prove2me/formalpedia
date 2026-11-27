-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.coeffIn_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:11:33.297226+00:00
-- url     : https://prove2.me/submissions/dfac8276-11be-4514-8b19-21126596d56e

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
theorem _root_.solution : CoeffIn W 0 (1 : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) := fun β => by
  rw [pow_zero, coeff_one]
  split_ifs
  · exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · exact zero_mem _
end ReciprocityTheory.ChartRestriction.G.T0
