-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.lv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:58:09.896417+00:00
-- url     : https://prove2.me/submissions/2080b38f-0e0c-4405-83a1-d4dc4945b3f1

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
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (c : ℂ) (v : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' (c • v) = c • liftVec k 1 r' v := by
  ext p
  simp only [liftVec, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
