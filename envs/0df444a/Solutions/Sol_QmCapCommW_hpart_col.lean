-- Prove2me | solution 1 for QmCapCommW.hpart_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:18.444057+00:00
-- url     : https://prove2.me/submissions/85c2e8aa-e79f-4de8-a294-b88a11e209d9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_CapelliOperatorCongruence
import Theorems.Thm_QmCapCommW_single_ct

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
theorem _root_.solution {k r : ℕ} {i : Fin (r + 1)} (a b : Fin (mdim k r i)) (c : Fin (2 * r + k + 1))
    (hcb : c ≠ posL k r i b) (hac : Hpk k r (posL k r i a) c = 0) (s : ℂ) (j : Fin (2 * r + k + 1)) :
    (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) + s • ((Hpk k r)⁻¹ *
      (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r)) j c = 0 := by
  rw [single_ct]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, hac, Ne.symm hcb]
end QmCapCommW
