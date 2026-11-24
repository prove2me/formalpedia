-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.hpk_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:58:09.152831+00:00
-- url     : https://prove2.me/submissions/6c649f2d-8ba2-44fe-80af-e56f9932bdec

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
theorem _root_.solution (k : ℕ) : Hpk k 0 = Matrix.diagonal (sg k) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Matrix.diagonal_apply, sg, iK, wI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | simp_all
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
