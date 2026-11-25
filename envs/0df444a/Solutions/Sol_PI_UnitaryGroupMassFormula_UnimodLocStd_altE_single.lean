-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.altE_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:45.249846+00:00
-- url     : https://prove2.me/submissions/1f43266d-3f14-4fad-98ec-cef37f2aeae9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsGoodForm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SatStdOfAll
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_stdH_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (L : PeriodPair) (v : m → ℂ) (n : ℕ) (j : m) (w : ℂ) :
    altE (stdH L m) v (n • Pi.single j w) = (n : ℝ) * (v j * conj w).im / area L := by
  classical
  unfold altE
  rw [stdH_apply]
  have hs : (∑ i, v i * conj ((n • Pi.single j w : m → ℂ) i)) = (n : ℂ) * (v j * conj w) := by
    rw [Finset.sum_eq_single j]
    · simp [nsmul_eq_mul]
      ring
    · intro i _ hi
      simp [hi]
    · simp
  rw [hs, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add, ← Complex.ofReal_natCast, Complex.im_ofReal_mul, div_eq_mul_inv]
end PI.UnitaryGroupMassFormula.UnimodLocStd
