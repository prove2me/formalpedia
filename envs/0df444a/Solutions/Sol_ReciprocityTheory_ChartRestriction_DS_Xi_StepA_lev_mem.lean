-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lev_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:43.125012+00:00
-- url     : https://prove2.me/submissions/289b0f30-174f-457b-b393-c8bc75b7ac60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RankOneLeviComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_mat_ext_lev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lev_conjT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_Hpk_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_Hpk_mulVec_e0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_hermMatrix_last_basis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lev_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_levi_fixes_base_vector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_levi_fixes_last_basis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
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
theorem _root_.solution {g : Mat k r'} (hg : g ∈ GV k r') : ιLev k 1 r' g ∈ GV k (1 + r') := by
  have hg' : gᴴ * Hpk k r' * g = Hpk k r' := hg
  show (ιLev k 1 r' g)ᴴ * Hpk k (1 + r') * ιLev k 1 r' g = Hpk k (1 + r')
  rw [lev_conjT]
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, Hpk_mulVec_e0, levi_fixes_last_basis]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, hermMatrix_last_basis, levi_fixes_base_vector]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift, Hpk_lift]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
