-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.iM_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:47:25.208793+00:00
-- url     : https://prove2.me/submissions/086ce6e3-8644-4ab5-8d9e-72b008a1a270

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_JOrbBoundB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.S0 ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
theorem _root_.solution (j : Fin (2 * r' + k + 1)) : (iM k r' j).val = j.val + 1 := rfl
end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
