-- Prove2me | solution 1 for WeierstrassCurve.subst_zero_X_fgSlope
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/747ef4f9-1d54-53d4-951d-9e12a96d8d50

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_subst_zero_X_fgSlope

set_option autoImplicit false

open FormalGroup

theorem solution
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    MvPowerSeries.subst ![(0 : PowerSeries R), PowerSeries.X] W.fgSlope
      = PowerSeries.mk fun n => PowerSeries.coeff (n + 1) W.formalW := by
  classical
  have hE : MvPowerSeries.HasSubst (![(0 : PowerSeries R), PowerSeries.X] : Fin 2 → PowerSeries R) :=
    FormalGroup.hasSubst_invDiff (R := R)
  ext n
  rw [PowerSeries.coeff_mk, show PowerSeries.coeff n (MvPowerSeries.subst ![(0 : PowerSeries R), PowerSeries.X] W.fgSlope)
      = MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.subst ![(0 : PowerSeries R), PowerSeries.X] W.fgSlope) from rfl,
    MvPowerSeries.coeff_subst hE]
  have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s m => ((![(0 : PowerSeries R), PowerSeries.X] : Fin 2 → PowerSeries R) s) ^ m)
      = (0 : PowerSeries R) ^ (d 0) * PowerSeries.X ^ (d 1) := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    rfl
  have hcX : ∀ m k : ℕ, MvPowerSeries.coeff (Finsupp.single () k) (PowerSeries.X ^ m : PowerSeries R) = if k = m then 1 else 0 :=
    fun m k => PowerSeries.coeff_X_pow k m
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [finsum_eq_single _ (Finsupp.single 1 n)]
  · rw [hprod, W.coeff_fgSlope]
    simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne h10, pow_zero, one_mul, _root_.zero_add,
      Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne (Ne.symm h10), _root_.add_zero, hcX, smul_eq_mul]
    simp only [ite_true, mul_one]

  · intro d hd
    rw [hprod]
    by_cases h0 : d 0 = 0
    · have h1 : d 1 ≠ n := by
        intro h1; apply hd; ext i; fin_cases i <;> simp [h0, h1]
      rw [h0, pow_zero, one_mul, hcX, if_neg (Ne.symm h1), smul_zero]
    · rw [zero_pow h0, zero_mul, map_zero, smul_zero]

end S_WeierstrassCurve_subst_zero_X_fgSlope
end P2MW
export P2MW.S_WeierstrassCurve_subst_zero_X_fgSlope (solution)
