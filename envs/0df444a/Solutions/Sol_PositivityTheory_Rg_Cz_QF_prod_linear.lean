-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QF.prod_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:12.890798+00:00
-- url     : https://prove2.me/submissions/793f8887-1722-49eb-a15f-60fd28b358af

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.QF
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {A : Type} [Ring A] [Algebra ℂ A]
omit [Algebra ℂ A]
namespace PositivityTheory.Rg.Cz.QF
theorem _root_.solution (m : ℕ) (c : Fin m → A) :
    (List.ofFn fun k : Fin m => X + C (c k)).prod.natDegree ≤ m ∧
      (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff m = 1 ∧
      ∀ j, j + 1 = m → (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff j = ∑ k, c k := by
  induction m with
  | zero =>
    refine ⟨by simp, by simp, fun j hj => by omega⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun k => c k.castSucc)
    have e : (List.ofFn fun k : Fin (m + 1) => X + C (c k)).prod =
        (List.ofFn fun k : Fin m => X + C (c k.castSucc)).prod * (X + C (c (Fin.last m))) := by
      rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
    rw [e]
    have hP : (List.ofFn fun k : Fin m => X + C (c k.castSucc)).prod.coeff (m + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    refine ⟨?_, ?_, ?_⟩
    · refine natDegree_mul_le.trans (add_le_add h1 ?_)
      exact (natDegree_add_le _ _).trans (max_le natDegree_X_le (by rw [natDegree_C]; exact zero_le_one))
    · rw [mul_add, coeff_add, coeff_mul_C, coeff_mul_X, h2, hP, zero_mul, add_zero]
    · intro j hj
      obtain rfl : j = m := by omega
      rw [Fin.sum_univ_castSucc, mul_add, coeff_add, coeff_mul_C, h2, one_mul]
      congr 1
      rcases j with _ | j
      · simp
      · rw [coeff_mul_X]
        exact h3 j rfl
end PositivityTheory.Rg.Cz.QF
