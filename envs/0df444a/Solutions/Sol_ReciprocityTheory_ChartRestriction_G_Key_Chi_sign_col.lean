-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.sign_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:58.19365+00:00
-- url     : https://prove2.me/submissions/02206ac7-a9b1-4551-bdca-d18a6c510979

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenFin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_mem


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
theorem _root_.solution (k : Fin g) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hsupp : ∀ r, M r (Sum.inl k) = if r = Sum.inl k then s else 0) :
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ r,
      (O * M) r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by
  classical
  rcases hs with rfl | rfl
  · refine ⟨1, (spH g).one_mem, colsFixed_one _, fun r => ?_⟩
    rw [Matrix.one_mul, hsupp r, Matrix.one_apply]
  · let D : Matrix (Fin g) (Fin g) ℤ := Matrix.diagonal fun i => if i = k then -1 else 1
    have hD : D * D = 1 := by
      simp only [D, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      split_ifs <;> norm_num
    let U : (Matrix (Fin g) (Fin g) ℤ)ˣ := ⟨D, D, hD, hD⟩
    refine ⟨spDiag U, spDiag_mem U, fun i hi => ?_, fun r => ?_⟩
    · have hik : i ≠ k := fun h => by subst h; exact lt_irrefl _ hi
      constructor <;> intro r <;> rcases r with a | a <;>
        simp [spDiag, U, D, Matrix.one_apply, Matrix.diagonal_apply, Matrix.fromBlocks] <;>
        split_ifs <;> simp_all
    · rw [Matrix.mul_apply, Fintype.sum_sum_type]
      rcases r with a | a <;>
        simp [spDiag, U, D, hsupp, Matrix.one_apply, Matrix.diagonal_apply, Matrix.fromBlocks] <;>
        split_ifs <;> simp_all
end ReciprocityTheory.ChartRestriction.G.Key.Chi
