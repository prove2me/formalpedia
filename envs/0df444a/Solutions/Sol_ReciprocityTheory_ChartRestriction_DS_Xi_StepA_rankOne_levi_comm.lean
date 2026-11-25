-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.rankOne_levi_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:34.205005+00:00
-- url     : https://prove2.me/submissions/8b506621-5000-4c42-8eae-fd8d5152d7e5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RankOneLeviComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_mat_ext_lev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lev_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_levi_fixes_base_vector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_levi_fixes_last_basis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_long_weyl_sends_base_to_dual
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_rankOneMatrix_last_basis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_rankOneMatrix_lift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos



set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (c : ℂ) (g : Mat k r') : w0 k r' c * ιLev k 1 r' g = ιLev k 1 r' g * w0 k r' c := by
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, long_weyl_sends_base_to_dual, Matrix.mulVec_smul, levi_fixes_last_basis]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, rankOneMatrix_last_basis, Matrix.mulVec_smul, levi_fixes_base_vector]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift, rankOneMatrix_lift]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
