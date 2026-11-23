-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spTransl_mul_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:01.834285+00:00
-- url     : https://prove2.me/submissions/cb38557f-2bf6-4f9c-86bc-9002acd5cbd5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution (S : Matrix (Fin g) (Fin g) ℤ) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (i : Fin g) (p : Fin g ⊕ Fin g) : (spTransl S * M) (Sum.inr i) p = M (Sum.inr i) p := by
  simp [spTransl, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
