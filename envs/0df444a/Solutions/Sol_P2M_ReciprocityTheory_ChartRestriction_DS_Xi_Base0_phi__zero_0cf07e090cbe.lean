-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__zero_0cf07e090cbe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:01:54.849024+00:00
-- url     : https://prove2.me/submissions/06b04477-e094-4858-8688-bad9ca6abcc4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__eq_e56a32e21c12

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
theorem _root_.solution (hk : 1 ≤ k) (i : Fin (2 * 0 + k + 1)) (h1 : i ≠ iW k) (h2 : i ≠ iK k) :
    phiV' k 0 0 i = 0 := by
  rw [phi'_eq hk]
  simp [bvec, h1, h2]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
