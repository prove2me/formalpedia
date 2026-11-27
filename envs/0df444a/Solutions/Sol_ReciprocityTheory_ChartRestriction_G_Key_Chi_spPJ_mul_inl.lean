-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spPJ_mul_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:28:20.855309+00:00
-- url     : https://prove2.me/submissions/d5ef0657-00b4-40ec-bdac-0eae8b48a3eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sum_eJ

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
theorem _root_.solution (j : Fin g) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g)
    (p : Fin g ⊕ Fin g) :
    (spPJ j * M) (Sum.inl i) p = if i = j then M (Sum.inr j) p else M (Sum.inl i) p := by
  simp only [spPJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, sum_eJ]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  split_ifs with h
  · subst h
    ring
  · ring
end ReciprocityTheory.ChartRestriction.G.Key.Chi
