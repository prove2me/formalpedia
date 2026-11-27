-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.J_mul_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:28:33.465257+00:00
-- url     : https://prove2.me/submissions/e479585f-ffed-4f33-b742-ba1ed2e6c7d1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
private theorem J_mul_apply_inl (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (j : Fin g)
    (q : Fin g ⊕ Fin g) : (J (Fin g) ℤ * M) (Sum.inl j) q = -M (Sum.inr j) q := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
end

set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (j : Fin g) (q : Fin g ⊕ Fin g) :
    (J (Fin g) ℤ * M) (Sum.inl j) q = -M (Sum.inr j) q := by
  exact J_mul_apply_inl M j q
end ReciprocityTheory.ChartRestriction.G.Key.Chi
