-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.inWb_iK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:55:21.303251+00:00
-- url     : https://prove2.me/submissions/4a34cdb6-3411-417a-bb4c-bcbdd6c2a6bc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne

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
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution (k : ℕ) : inWb k 0 (bvec (iK k)) := by
  intro i hi
  exfalso
  have := i.isLt
  rcases hi with h | h <;> omega
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
