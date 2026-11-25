-- Prove2me | solution 1 for PI.AlgValsFin.W.locVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:11.662442+00:00
-- url     : https://prove2.me/submissions/42c6c6aa-3ad7-4224-bba6-c8c3fb6fe9e6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ValuedAtFin
import Theorems.Thm_PI_AlgValsFin_W_valued_atFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution : LocVal L := by
  intro χ v k hχ
  have hu : IsUnifAt v (atFin v (unif v)) := Classical.choose_spec (exists_unif v)
  unfold IsUnifAt at hu
  have hunit : IsUnitAt v (atFin v k * (atFin v (unif v) ^ ordF v k)⁻¹) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, hu,
      valued_atFin, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one,
      mul_inv_cancel₀ WithZero.exp_ne_zero]
  have h1 := hχ _ hunit
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h1
  rw [h1]
  rfl
end PI.AlgValsFin.W
