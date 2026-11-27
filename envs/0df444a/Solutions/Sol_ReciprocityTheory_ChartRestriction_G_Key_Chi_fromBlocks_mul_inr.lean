-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.fromBlocks_mul_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:28:56.164551+00:00
-- url     : https://prove2.me/submissions/e5469c9c-81e9-4ebb-890c-618ea9b66e44

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
    (fromBlocks A B C D * M) (Sum.inr i) p =
      (∑ j, C i j * M (Sum.inl j) p) + ∑ j, D i j * M (Sum.inr j) p := by

  simp [Matrix.mul_apply, Fintype.sum_sum_type]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
