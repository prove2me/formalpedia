-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:07.024652+00:00
-- url     : https://prove2.me/submissions/9c39cb36-87ed-40da-8b04-f8419e41ff63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
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
theorem _root_.solution (j : Fin (2 * r' + k + 1)) : liftVec k 1 r' (bvec j) = bvec (mp k r' j) := by
  funext p
  have hj := j.isLt
  have hp0 := p.isLt
  simp only [liftVec, bvec, Pi.single_apply, mp, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> first | rfl | omega
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
