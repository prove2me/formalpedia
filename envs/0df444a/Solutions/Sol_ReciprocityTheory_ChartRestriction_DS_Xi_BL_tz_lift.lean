-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.tz_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:05:43.500905+00:00
-- url     : https://prove2.me/submissions/fbdaf31e-acd2-496c-bbaf-af3fa3b46338

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_herm_lv

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
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (z1 : Fin (2 * r' + k + 1) → ℂ) : Tz k (1 + r') (liftVec k 1 r' z1) = Tz k r' z1 := by
  unfold Tz
  rw [herm_lv]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
