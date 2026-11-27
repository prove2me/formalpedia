-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spDiag_rk_mul_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:29:04.888065+00:00
-- url     : https://prove2.me/submissions/bc11b87c-0c09-450a-84ef-e8b1ca4a9ff9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_rkU_val

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
theorem _root_.solution (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g) (p : Fin g ⊕ Fin g) :
    (spDiag (rkU u v h) * M) (Sum.inl i) p = M (Sum.inl i) p + u i * ∑ l, v l * M (Sum.inl l) p := by
  simp only [spDiag, rkU_val, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun l _ => by ring)
end ReciprocityTheory.ChartRestriction.G.Key.Chi
