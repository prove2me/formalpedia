-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.tt_0su
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:48.168114+00:00
-- url     : https://prove2.me/submissions/aefe8c9a-75a7-44a6-9a93-57fe64cfa75e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange

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
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}
variable (τ : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℂ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (a : Fin (r' + 1)) : tt τ 0 (su a) = 0 := by
  simp [tt, su]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
