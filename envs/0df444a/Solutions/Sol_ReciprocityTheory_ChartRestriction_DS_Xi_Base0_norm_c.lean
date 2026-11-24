-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.norm_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:58:15.182643+00:00
-- url     : https://prove2.me/submissions/06ef7b89-3c70-426e-98f7-030f0649cfb4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne

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
theorem _root_.solution : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ = (Real.sqrt 2)⁻¹ := by
  rw [norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg 2)]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
