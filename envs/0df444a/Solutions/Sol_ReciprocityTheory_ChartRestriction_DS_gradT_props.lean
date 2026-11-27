-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.gradT_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:24:45.33805+00:00
-- url     : https://prove2.me/submissions/4758c343-4cda-4899-8f1e-2470082d4d65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gradT_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gradT_cpT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gradT_cmT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eT_gradT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fockT_anti_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fock_inv_sq


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
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) :
    gradT (N := N) (n := n) * gradT = 1 ∧ gradT * dOp ε (eT E) cpT = -(dOp ε (eT E) cpT * gradT) ∧
      gradT * dOp' ε (eT E) cmT = -(dOp' ε (eT E) cmT * gradT) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gradT_eq, ← map_mul, fock_inv_sq, map_one]
  · exact fockT_anti_sum _ _ _ (fun i a => eT E a i) (fun i a => cpT i a) (fun i a => (eT_gradT E a i).symm)
      (fun i a => gradT_cpT i a)
  · simp only [dOp', mul_neg, neg_mul]
    rw [fockT_anti_sum _ _ _ (fun i a => eT E i a) (fun i a => cmT i a) (fun i a => (eT_gradT E i a).symm)
      (fun i a => gradT_cmT i a)]
end ReciprocityTheory.ChartRestriction.DS
