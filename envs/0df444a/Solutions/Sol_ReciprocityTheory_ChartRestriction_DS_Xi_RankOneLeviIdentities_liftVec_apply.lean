-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.liftVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:49:09.306263+00:00
-- url     : https://prove2.me/submissions/721f692b-89df-4301-b33e-648ffed7391e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
theorem _root_.solution (z : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1)) :
    liftVec k 1 r' z p = if h : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then z ⟨p.val - 1, by omega⟩ else 0 :=
  rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
