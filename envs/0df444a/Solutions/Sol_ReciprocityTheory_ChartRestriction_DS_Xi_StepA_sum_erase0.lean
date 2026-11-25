-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.sum_erase0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:36.567586+00:00
-- url     : https://prove2.me/submissions/d234e222-8512-4c10-9655-77bac07f0f19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InnerCLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentShiftEqLevelExponent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_sum_sc

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
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (f : Fin (1 + r' + 1) → ℝ) : ∑ l ∈ Finset.univ.erase 0, f l = ∑ l : Fin (r' + 1), f (sc r' l) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_sc]; ring
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
