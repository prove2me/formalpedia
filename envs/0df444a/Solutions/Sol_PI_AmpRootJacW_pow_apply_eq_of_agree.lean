-- Prove2me | solution 1 for PI.AmpRootJacW.pow_apply_eq_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:40.65297+00:00
-- url     : https://prove2.me/submissions/8f27432a-892e-4ee3-af5f-f80aad578fcb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
import Theorems.Thm_PI_AmpRootJacW_sUp_pow
import Theorems.Thm_PI_AmpRootJacW_pow_agree

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
theorem _root_.solution {V V' : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) (hV' : SUp V') (g : ℕ)
    (h : ∀ a b : Fin n, b.val < a.val + g → V a b = V' a b) (m : ℕ) (i j : Fin n)
    (hij : j.val ≤ i.val + g) : (V ^ (m + 1 + 1)) i j = (V' ^ (m + 1 + 1)) i j := by
  rw [pow_succ, pow_succ V', Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : k.val < i.val + (m + 1)
  · rw [sUp_pow hV (m + 1) i k hk, sUp_pow hV' (m + 1) i k hk, zero_mul, zero_mul]
  · by_cases hjk : j.val ≤ k.val
    · rw [hV k j hjk, hV' k j hjk, mul_zero, mul_zero]
    · have h' : ∀ a b : Fin n, b.val ≤ a.val + (g - 1) → V a b = V' a b := fun a b hab => h a b (by omega)
      rw [pow_agree hV hV' (g - 1) h' m i k (by omega), h k j (by omega)]
end PI.AmpRootJacW
