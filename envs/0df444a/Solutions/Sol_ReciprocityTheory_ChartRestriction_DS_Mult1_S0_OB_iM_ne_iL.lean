-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.iM_ne_iL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:13:56.123791+00:00
-- url     : https://prove2.me/submissions/87c748f6-4f86-4084-8661-829a74152ea4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_JOrbBoundB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_iL_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_iM_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.iL_val
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.iM_val

set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.S0 ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
theorem _root_.solution (j : Fin (2 * r' + k + 1)) : iM k r' j ≠ iL k r' := by
  have := j.isLt; rw [Ne, Fin.ext_iff, iM_val, iL_val]; omega
end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
