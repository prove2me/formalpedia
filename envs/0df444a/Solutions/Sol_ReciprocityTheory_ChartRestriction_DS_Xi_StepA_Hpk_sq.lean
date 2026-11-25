-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:54:52.381264+00:00
-- url     : https://prove2.me/submissions/c571df5e-db39-4dbb-aa79-1f685d1af61b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_mat_eq_of_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_Hpk_mulVec_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec fun v => by rw [← Matrix.mulVec_mulVec, Hpk_mulVec_mulVec, Matrix.one_mulVec]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
