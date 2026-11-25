-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QF.coeff_qdetPoly_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:36.664377+00:00
-- url     : https://prove2.me/submissions/72ece3a2-211f-4d4c-8da7-a138d69d07bd

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_natDegree_prod_ne_one
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_tmPoly_diag

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
namespace PositivityTheory.Rg.Cz.QF
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (j : ℕ) (hj : n ≤ j + 1) :
    (qdetPoly E).coeff j = (List.ofFn fun k : Fin n => X + C (E k k - algebraMap ℂ A ((k : ℕ) : ℂ))).prod.coeff j := by
  rw [qdetPoly, finset_sum_coeff, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, C_1, one_mul, Equiv.Perm.one_apply, tmPoly_diag]
  · intro σ _ hσ
    rw [coeff_C_mul]
    have := natDegree_prod_ne_one E hσ
    rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end PositivityTheory.Rg.Cz.QF
