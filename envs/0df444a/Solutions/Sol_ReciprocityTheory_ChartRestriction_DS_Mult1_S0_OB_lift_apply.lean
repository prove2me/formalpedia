-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.lift_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:04:44.670661+00:00
-- url     : https://prove2.me/submissions/ef2dd6b2-0db9-4470-9743-4bf8047048e4

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
theorem _root_.solution (y : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1)) : liftVec k 1 r' y p =
    if hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then y ⟨p.val - 1, by omega⟩ else 0 := rfl
end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
