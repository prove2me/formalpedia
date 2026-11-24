-- Prove2me | solution 1 for QmCapCommW.hpk_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:34:36.281506+00:00
-- url     : https://prove2.me/submissions/10644a23-3ec9-4d92-bcf0-7a12c735d606

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
theorem _root_.solution {k r : ℕ} (i : Fin (r + 1)) (p : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    Hpk k r (posL k r i p) (eI k r a) = 0 ∧ Hpk k r (posL k r i p) (esI k r a) = 0 := by
  have hp := p.isLt
  have hi := i.isLt
  unfold mdim at hp
  constructor <;> simp only [Hpk, posL, eI, esI, Fin.ext_iff, Fin.val_mk] <;> split_ifs <;>
    first | rfl | (exfalso; omega)
end QmCapCommW
