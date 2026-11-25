-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rhoC_add_rhoHol_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:08.814275+00:00
-- url     : https://prove2.me/submissions/e0aa20c6-45c2-468c-bb98-9c05e19696a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_card_same_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_card_same_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carU_pOf_add_qOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (a : Fin n) :
    (rhoC ε + rhoHol ε) a = ((n : ℝ) - 1) / 2 - (carUPos ε a : ℝ) := by
  have h1 : ((univ.filter fun b => ε b = ε a).card : ℝ) =
      ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) + 1 +
        ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := by
    exact_mod_cast card_same_split ε a
  have h2 := card_same_eq ε a
  have h3 : (pOf ε : ℝ) + (qOf ε : ℝ) = n := by exact_mod_cast carU_pOf_add_qOf ε
  simp only [Pi.add_apply, rhoC, rhoHol, carUPos]
  cases h : ε a <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢ <;> rw [h2] at h1 <;> push_cast <;>
    linarith
end ReciprocityTheory.ChartRestriction.DS
