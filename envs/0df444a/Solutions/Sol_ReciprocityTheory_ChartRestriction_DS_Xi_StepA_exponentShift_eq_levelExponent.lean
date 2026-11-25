-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.exponentShift_eq_levelExponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:50.676048+00:00
-- url     : https://prove2.me/submissions/9dbe0ea9-e97d-446c-9194-0ea8373f9763

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InnerCLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentShiftEqLevelExponent

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
theorem _root_.solution (hk : 1 ≤ k) (l : Fin (1 + r' + 1)) : s0N (1 + r') (k - 1) l = s0 k (1 + r') l := by
  unfold s0N s0
  split_ifs
  · rfl
  · rw [Nat.cast_sub hk]; push_cast; ring
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
