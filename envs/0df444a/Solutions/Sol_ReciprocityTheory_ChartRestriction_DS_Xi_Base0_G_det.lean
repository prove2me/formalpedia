-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.G_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:04.341027+00:00
-- url     : https://prove2.me/submissions/886d5e42-6842-41b7-945c-5326ce03a168

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_G_left

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
theorem _root_.solution {g : Mat k 0} (hg : g ∈ GV k 0) : g.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (G_left hg)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
