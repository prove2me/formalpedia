-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mulVec_e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:50.485878+00:00
-- url     : https://prove2.me/submissions/6721effc-de67-4aec-a57b-747c701a7c16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_last_basis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_mulVec_first_basis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last

set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution : Hpk k (1 + r') *ᵥ e0 k r' = es0 k r' := by
  rw [mulVec_first_basis]
  funext p
  rw [last_basis_apply]
  have h0 : ((0 : Fin (2 * (1 + r') + k + 1)) : ℕ) = 0 := by simp
  have hp0 := p.isLt
  simp only [Hpk, Fin.ext_iff, h0, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> first | rfl | omega
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
