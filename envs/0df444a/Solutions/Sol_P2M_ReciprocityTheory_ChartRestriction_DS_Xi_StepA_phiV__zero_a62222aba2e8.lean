-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_phiV__zero_a62222aba2e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:03.111321+00:00
-- url     : https://prove2.me/submissions/92da7a6c-1844-4e5e-9c43-c6ed7fa35a05

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_hermMatrix_last_basis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_phiV_zero
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
theorem _root_.solution : phiV' k (1 + r') 0 = e0 k r' := by
  simp only [phiV', phiV_zero, hermMatrix_last_basis]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
