-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.lift_iL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:39.568714+00:00
-- url     : https://prove2.me/submissions/8c7ebb85-0185-402b-b76c-ed2da570e8c6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_JOrbBoundB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_first_index_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_iL_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_iM_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_middle_ne_first_index
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_first_ne_middle_index
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_iM_ne_iL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_iL_ne_iM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_first_ne_last_index
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_last_ne_first_index
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_iM_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_lift_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_lifted_vector_first
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.first_index_val
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.iL_val
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.iM_val
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.middle_ne_first_index
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.first_ne_middle_index
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.iM_ne_iL
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.iL_ne_iM
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.first_ne_last_index
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.last_ne_first_index
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.iM_inj
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.lifted_vector_first

set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.S0 ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
theorem _root_.solution (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (iL k r') = 0 := by
  rw [lift_apply, dif_neg (by simp only [iL_val]; omega)]
end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
