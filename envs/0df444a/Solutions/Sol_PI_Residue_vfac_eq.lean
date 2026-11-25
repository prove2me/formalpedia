-- Prove2me | solution 1 for PI.Residue.vfac_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:39.381815+00:00
-- url     : https://prove2.me/submissions/2c511b29-1167-4278-b250-139743aa14af

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution (K : Type) [Field K] [NumberField K] :
    vfac K = ENNReal.ofReal (2 ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K) := by
  rw [vfac, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow Real.pi_pos.le, ENNReal.ofReal_ofNat, ← NNReal.coe_real_pi,
    ENNReal.ofReal_coe_nnreal]
end PI.Residue
