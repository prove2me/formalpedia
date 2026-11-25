-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_LCG_hsN_nonneg__4978ee1409bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:48:01.549508+00:00
-- url     : https://prove2.me/submissions/858a26d8-5565-4e9c-95b7-5b7aec11357e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatticeIsDiscreteGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.LatCountG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN A := by
  unfold hsN
  exact Real.sqrt_nonneg _
end PI.UnitaryGroupMassFormula.LCG
