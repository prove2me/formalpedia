-- Prove2me | solution 1 for QmCapCommW.hpk_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:56:35.902976+00:00
-- url     : https://prove2.me/submissions/3d89578f-e565-4178-b233-711cb90c8d0c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_CapelliOperatorCongruence
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open QmCapCommW
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace QmCapCommW
theorem _root_.solution (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (hpkFacts k r).2.1
end QmCapCommW
