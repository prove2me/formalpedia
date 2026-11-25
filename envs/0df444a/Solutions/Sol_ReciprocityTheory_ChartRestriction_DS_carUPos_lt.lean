-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.carUPos_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:44.306232+00:00
-- url     : https://prove2.me/submissions/f8e57fc8-949f-4d2f-9232-2a64396c25ed

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
theorem _root_.solution (ε : Fin n → Bool) (a : Fin n) : carUPos ε a < n := by
  have h1 := card_same_split ε a
  have h2 := card_same_eq ε a
  have h3 := carU_pOf_add_qOf ε
  unfold carUPos
  cases h : ε a <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢ <;> omega
end ReciprocityTheory.ChartRestriction.DS
