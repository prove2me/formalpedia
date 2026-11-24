-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.herm0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:57:47.451604+00:00
-- url     : https://prove2.me/submissions/10500148-d224-41be-b364-8d11209fdd80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_hpk_mulVec

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
theorem _root_.solution (v w : Fin (2 * 0 + k + 1) → ℂ) :
    herm (Hpk k 0) v w = ∑ i, star (w i) * (sg k i * v i) := by
  simp only [herm, dotProduct, Pi.star_apply, hpk_mulVec]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
