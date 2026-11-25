-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.row_inr_of_col_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:52.504832+00:00
-- url     : https://prove2.me/submissions/0a476b3b-1b5f-4bf5-9bd0-13ed59d05d7b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_mul_col_of_unit

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
theorem _root_.solution {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) {i : Fin g}
    (h : ∀ r, M r (Sum.inl i) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl i))
    (q : Fin g ⊕ Fin g) :
    M (Sum.inr i) q = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Sum.inr i) q := by

  have h1 : Mᵀ * J (Fin g) ℤ * M = J (Fin g) ℤ := SymplecticGroup.mem_iff'.mp hM
  have h2 := congrFun (congrFun h1 q) (Sum.inl i)
  rw [mul_col_of_unit h, Matrix.mul_apply] at h2
  have hJ : ∀ r, J (Fin g) ℤ r (Sum.inl i) = if r = Sum.inr i then 1 else 0 := by
    intro r
    rcases r with r | r <;> by_cases hri : r = i <;> simp [Matrix.J, Matrix.one_apply, hri]
  simp_rw [hJ, Matrix.transpose_apply] at h2
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  rw [h2, Matrix.one_apply]
  by_cases hq : q = Sum.inr i
  · subst hq
    simp
  · rw [if_neg hq, if_neg (Ne.symm hq)]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
