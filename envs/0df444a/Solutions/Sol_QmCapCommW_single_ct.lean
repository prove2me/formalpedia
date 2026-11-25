-- Prove2me | solution 1 for QmCapCommW.single_ct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:54.99635+00:00
-- url     : https://prove2.me/submissions/d3fd4b17-dc44-4830-8fa4-73138d9e7e9e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_CapelliOperatorCongruence

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
theorem _root_.solution {n : ℕ} (a b : Fin n) : (Matrix.single a b (1 : ℂ))ᴴ = Matrix.single b a 1 := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs <;> simp_all
end QmCapCommW
