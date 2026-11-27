-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.fromBlocks_mul_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:28:49.698056+00:00
-- url     : https://prove2.me/submissions/363d8880-2d5d-499a-adba-1d7c207a5a2f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase

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
theorem _root_.solution (A B C D : Matrix (Fin g) (Fin g) ℤ)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g) (p : Fin g ⊕ Fin g) :
    (fromBlocks A B C D * M) (Sum.inl i) p =
      (∑ j, A i j * M (Sum.inl j) p) + ∑ j, B i j * M (Sum.inr j) p := by

  simp [Matrix.mul_apply, Fintype.sum_sum_type]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
