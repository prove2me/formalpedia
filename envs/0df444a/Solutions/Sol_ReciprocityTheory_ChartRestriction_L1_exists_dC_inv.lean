-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.exists_dC_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:32.534184+00:00
-- url     : https://prove2.me/submissions/6016193a-f00b-4259-8d1c-6150838c4552

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : ∃ v : PowerSeries ℤ, PowerSeries.coeff 0 v = 1 ∧
    ∀ H : PowerSeries ℂ, PowerSeries.X * H = v.map (Int.castRingHom ℂ) * (dC * H) := by
  set u : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) dZ with hu
  have hd0 : PowerSeries.coeff 0 dZ = 0 := by
    rw [dZ, PowerSeries.coeff_mk]
    simp [e4Z, e6Z, pow_succ, PowerSeries.coeff_mul]
  have hd1 : PowerSeries.coeff 1 dZ = 1 := by
    rw [dZ, PowerSeries.coeff_mk]
    simp [e4Z, e6Z, pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ] <;> norm_num
  have hXu : dZ = PowerSeries.X * u := by
    ext n
    rcases n with _ | n
    · rw [hd0, PowerSeries.coeff_zero_X_mul]
    · rw [PowerSeries.coeff_succ_X_mul, hu, PowerSeries.coeff_mk]
  have hu0 : PowerSeries.constantCoeff u = ((1 : ℤˣ) : ℤ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hu, PowerSeries.coeff_mk, zero_add, hd1, Units.val_one]
  refine ⟨PowerSeries.invOfUnit u 1, ?_, fun H => ?_⟩
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
  · have hinv := PowerSeries.mul_invOfUnit u 1 hu0
    have hdC : dC = PowerSeries.X * u.map (Int.castRingHom ℂ) := by
      rw [dC, hXu, map_mul, PowerSeries.map_X]
    rw [hdC]
    have h1 : (u.map (Int.castRingHom ℂ)) * (PowerSeries.invOfUnit u 1).map (Int.castRingHom ℂ) = 1 := by
      rw [← map_mul, hinv, map_one]
    linear_combination (-(PowerSeries.X * H)) * h1
end ReciprocityTheory.ChartRestriction.L1
