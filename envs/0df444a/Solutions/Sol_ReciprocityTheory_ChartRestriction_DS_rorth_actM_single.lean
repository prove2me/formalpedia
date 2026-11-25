-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rorth_actM_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:31.173633+00:00
-- url     : https://prove2.me/submissions/62126474-7731-4b32-8947-cf1fe32c0afe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Matrix.single a b (1 : ℂ)) = E a b := by
  unfold actM
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [Matrix.single_apply_same]
  · intro b' _ hb; rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hb), zero_smul]
  · simp
  · intro a' _ ha
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [Matrix.single_apply_of_row_ne (Ne.symm ha), zero_smul]
  · simp
end ReciprocityTheory.ChartRestriction.DS
