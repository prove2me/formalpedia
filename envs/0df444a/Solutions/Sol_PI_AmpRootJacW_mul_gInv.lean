-- Prove2me | solution 1 for PI.AmpRootJacW.mul_gInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:06.237061+00:00
-- url     : https://prove2.me/submissions/502da793-6385-465a-853b-e0eb76fe28b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
import Theorems.Thm_PI_AmpRootJacW_sUp_neg
import Theorems.Thm_PI_AmpRootJacW_sUp_pow_eq_zero

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
theorem _root_.solution {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) : (1 + V) * gInv V = 1 := by
  unfold gInv
  have h := mul_neg_geom_sum (-V) (n + 2)
  rw [sub_neg_eq_add] at h
  rw [h, sUp_pow_eq_zero (sUp_neg hV) (n + 2) (by omega), sub_zero]
end PI.AmpRootJacW
