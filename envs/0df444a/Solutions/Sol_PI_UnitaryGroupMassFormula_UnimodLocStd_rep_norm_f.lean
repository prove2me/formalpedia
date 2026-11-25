-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_norm_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:02:51.001801+00:00
-- url     : https://prove2.me/submissions/5c00d3ba-9a76-4809-ba3a-9c87b76523b8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_elt_norm
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
variable (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) (x y : ℤ) (i₀ : m) :
    stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀) =
      repKappa a b d ha hd lam hlam * ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℂ) := by
  rw [rep_H_apply, Fintype.sum_eq_single i₀ (fun i hi => by simp [fvec, hi])]
  simp only [fvec, Pi.single_eq_same]
  rw [rep_elt_norm a b c d lam hOK x y]
  unfold repKappa
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
