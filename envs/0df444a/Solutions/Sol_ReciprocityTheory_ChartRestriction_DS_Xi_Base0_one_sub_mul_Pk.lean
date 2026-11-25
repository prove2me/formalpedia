-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.one_sub_mul_Pk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:41:17.536833+00:00
-- url     : https://prove2.me/submissions/9bda904c-74e6-4b9b-a83f-65ede82e01d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_Pk_mul_self

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
theorem _root_.solution (k : ℕ) : (1 - 2 • Pk k) * Pk k = -Pk k := by
  rw [sub_mul, one_mul, smul_mul_assoc, Pk_mul_self, two_smul]
  abel
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
