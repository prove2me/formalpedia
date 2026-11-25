-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.fixedUnitary_mulVec_fixedIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:08:44.756738+00:00
-- url     : https://prove2.me/submissions/7bbd90fd-3166-4fa6-87f9-9f7de102a56b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_fixedUnitary_apply_fixedIndex_left

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
theorem _root_.solution {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (y : Fin (2 * 0 + k + 1) → ℂ) :
    (h *ᵥ y) (iK k) = y (iK k) := by
  simp [Matrix.mulVec, dotProduct, fixedUnitary_apply_fixedIndex_left hh]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
