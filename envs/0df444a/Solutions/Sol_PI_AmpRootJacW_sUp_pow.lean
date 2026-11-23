-- Prove2me | solution 1 for PI.AmpRootJacW.sUp_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:24.6138+00:00
-- url     : https://prove2.me/submissions/cb1bb4a9-d56c-4177-b583-1a102ac77235

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero

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
theorem _root_.solution {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) :
    ∀ (m : ℕ) (i j : Fin n), j.val < i.val + m → (V ^ m) i j = 0
  | 0, i, j, h => by
    rw [pow_zero, Matrix.one_apply, if_neg]
    rintro rfl; omega
  | m + 1, i, j, h => by
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.val < i.val + m
    · rw [solution hV m i l hl, zero_mul]
    · rw [hV l j (by omega), mul_zero]
end PI.AmpRootJacW
