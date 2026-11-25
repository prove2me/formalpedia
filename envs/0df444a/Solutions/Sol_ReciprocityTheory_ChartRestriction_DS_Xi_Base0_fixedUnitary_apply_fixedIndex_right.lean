-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.fixedUnitary_apply_fixedIndex_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:40.271874+00:00
-- url     : https://prove2.me/submissions/53fe083f-1029-41d7-a6ea-ce9cff539d2c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_fixedUnitary_projection_identities

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
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (i : Fin (2 * 0 + k + 1)) :
    h i (iK k) = if i = iK k then 1 else 0 := by
  have := congrFun (congrFun (fixedUnitary_projection_identities hh).2.1 i) (iK k)
  simpa [Pk, Matrix.mul_apply, Matrix.single_apply, eq_comm] using this
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
