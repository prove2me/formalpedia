-- Prove2me | solution 1 for PI.AmpRootJacW.sUp_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:33:47.808816+00:00
-- url     : https://prove2.me/submissions/e22b824a-f124-4609-9f91-246d27f3c7bf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
import Theorems.Thm_PI_AmpRootJacW_sUp_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.AmpRootJacW
variable {n : ℕ}
namespace PI.AmpRootJacW
theorem _root_.solution {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) (m : ℕ) (hm : n ≤ m) : V ^ m = 0 := by
  ext i j
  have hj := j.2
  simp only [Matrix.zero_apply]
  exact sUp_pow hV m i j (by omega)
end PI.AmpRootJacW
