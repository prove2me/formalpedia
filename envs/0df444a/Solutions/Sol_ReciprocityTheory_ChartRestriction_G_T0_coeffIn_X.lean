-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.coeffIn_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:32:35.062859+00:00
-- url     : https://prove2.me/submissions/922798ea-86d6-4b11-aaa6-f273202896e7

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
theorem _root_.solution (u : Fin (D + 2) × Fin (N + 1)) : CoeffIn W 0 (X u : MvPolynomial _ B) := fun β => by
  rw [pow_zero, coeff_X']
  split_ifs
  · exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · exact zero_mem _
end ReciprocityTheory.ChartRestriction.G.T0
