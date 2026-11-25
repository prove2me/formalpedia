-- Prove2me | solution 1 for PI.AlgValsFin.W.toNNReal_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:18:27.427404+00:00
-- url     : https://prove2.me/submissions/61b899ed-5b1c-44aa-bbd8-93f1116ba0cf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_FinprodNormEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution {e : NNReal} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  first
    | (simp [WithZero.exp, WithZeroMulInt.toNNReal_pos_apply he]; done)
    | (rw [WithZeroMulInt.toNNReal_pos_apply he WithZero.exp_ne_zero]; simp [WithZero.exp]; done)
    | rfl
end PI.AlgValsFin.W
