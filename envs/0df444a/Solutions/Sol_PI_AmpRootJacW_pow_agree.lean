-- Prove2me | solution 1 for PI.AmpRootJacW.pow_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:25.285721+00:00
-- url     : https://prove2.me/submissions/19336f16-ae65-4b49-8104-6a506bf860ef

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
theorem _root_.solution {V V' : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) (hV' : SUp V') (d : ℕ)
    (h : ∀ a b : Fin n, b.val ≤ a.val + d → V a b = V' a b) :
    ∀ (m : ℕ) (i j : Fin n), j.val ≤ i.val + d → (V ^ (m + 1)) i j = (V' ^ (m + 1)) i j
  | 0, i, j, hij => by rw [pow_one, pow_one]; exact h i j hij
  | m + 1, i, j, hij => by
    rw [pow_succ' V (m + 1), pow_succ' V' (m + 1), Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h1 : l.val ≤ i.val
    · rw [hV i l h1, hV' i l h1, zero_mul, zero_mul]
    by_cases h2 : j.val ≤ l.val
    · rw [sUp_pow hV (m + 1) l j (by omega), sUp_pow hV' (m + 1) l j (by omega), mul_zero, mul_zero]
    rw [h i l (by omega), solution hV hV' d h m l j (by omega)]
end PI.AmpRootJacW
