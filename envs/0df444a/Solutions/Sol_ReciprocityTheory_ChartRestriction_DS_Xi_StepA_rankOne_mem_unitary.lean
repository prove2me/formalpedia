-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.rankOne_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:28.957858+00:00
-- url     : https://prove2.me/submissions/bea18138-8485-4dc2-b65a-00b2672ea34c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_one_gv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_heis0_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_lev_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_inv_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {k r' : ℕ} (hOSM : OneStepMem) {c : ℂ} (hc : c ≠ 0) : w0 k r' c ∈ GV k (1 + r') := by
  have h := (hOSM k r' (0, 0) (0, 0) c hc 1 (ea_one_gv k r')).1
  rw [oneStep, ea_heis0_zero, ea_lev_one, ea_inv_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_one] at h
  exact h
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
