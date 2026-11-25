-- Prove2me | solution 1 for PI.AddIntG.Wk.root_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:08.914686+00:00
-- url     : https://prove2.me/submissions/9e28d32c-0379-477e-8f85-93f5014f7b3c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
import Theorems.Thm_PI_AddIntG_Wk_omega_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) (j : Fin 2)
    {r : MvPowerSeries (Fin 2) ℂ_[p]} (hr : MvPowerSeries.constantCoeff r = 0)
    (hw : PowerSeries.subst r (wser wq) = lam wq * r + nu wq)
    (hG : G W r (lam wq * r + nu wq) = 0) :
    PowerSeries.subst r (omegaW W wq) * MvPowerSeries.pderiv ℂ_[p] j r *
      (3 * Acf W wq * r ^ 2 + 2 * Bcf W wq * r + Ccf W wq) =
      r * MvPowerSeries.pderiv ℂ_[p] j (lam wq) + MvPowerSeries.pderiv ℂ_[p] j (nu wq) := by
  set D := MvPowerSeries.pderiv ℂ_[p] j with hDdef
  have hω := omega_at h hr
  rw [hw] at hω
  have hD := congrArg D hG
  rw [map_zero] at hD
  simp only [G, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.map_algebraMap, smul_eq_mul, nsmul_eq_mul, smul_zero, zero_smul, mul_zero, zero_mul,
    add_zero, zero_add, Nat.cast_ofNat] at hD
  simp only [Gv] at hω
  simp only [Acf, Bcf, Ccf, cc]
  linear_combination (PowerSeries.subst r (omegaW W wq)) * hD -
    (r * D (lam wq) + D (nu wq)) * hω
end PI.AddIntG.Wk
