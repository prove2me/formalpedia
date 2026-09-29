-- Prove2me | solution 1 for WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/75c173c7-3889-5a4a-a012-45575e29df39

import Mathlib
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map

set_option autoImplicit false

open PowerSeries

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S) :
    (W.map f).formalW = PowerSeries.map f W.formalW ∧
      (W.map f).formalGroupLawFixed = MvPowerSeries.map f W.formalGroupLawFixed := by

  have hW : (W.map f).formalW = PowerSeries.map f W.formalW := by
    symm
    apply (W.map f).eq_formalW_of_constantCoeff_eq_zero
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, W.constantCoeff_formalW, map_zero]
    · have h := congrArg (PowerSeries.map f) W.formalW_eq
      simp only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X] at h
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
        WeierstrassCurve.map_a₆]
      exact h
  refine ⟨hW, ?_⟩

  have hinvP : ∀ (φ : PowerSeries R), PowerSeries.constantCoeff φ = 1 →
      PowerSeries.map f (φ.invOfUnit 1) = (PowerSeries.map f φ).invOfUnit 1 := by
    intro φ hφ
    have h1 : PowerSeries.map f φ * (PowerSeries.map f φ).invOfUnit 1 = 1 :=
      PowerSeries.mul_invOfUnit _ _ (by
        rw [Units.val_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
          PowerSeries.coeff_zero_eq_constantCoeff_apply, hφ, map_one])
    have h2 : PowerSeries.map f φ * PowerSeries.map f (φ.invOfUnit 1) = 1 := by
      rw [← map_mul, PowerSeries.mul_invOfUnit _ _ (by rw [Units.val_one]; exact hφ), map_one]
    calc PowerSeries.map f (φ.invOfUnit 1)
        = PowerSeries.map f (φ.invOfUnit 1) * (PowerSeries.map f φ * (PowerSeries.map f φ).invOfUnit 1) := by
          rw [h1, mul_one]
      _ = (PowerSeries.map f φ * PowerSeries.map f (φ.invOfUnit 1)) * (PowerSeries.map f φ).invOfUnit 1 := by ring
      _ = (PowerSeries.map f φ).invOfUnit 1 := by rw [h2, one_mul]
  have hinvM : ∀ (φ : MvPowerSeries (Fin 2) R), MvPowerSeries.constantCoeff φ = 1 →
      MvPowerSeries.map f (φ.invOfUnit 1) = (MvPowerSeries.map f φ).invOfUnit 1 := by
    intro φ hφ
    have h1 : MvPowerSeries.map f φ * (MvPowerSeries.map f φ).invOfUnit 1 = 1 :=
      MvPowerSeries.mul_invOfUnit _ _ (by
        rw [Units.val_one, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
          MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ, map_one])
    have h2 : MvPowerSeries.map f φ * MvPowerSeries.map f (φ.invOfUnit 1) = 1 := by
      rw [← map_mul, MvPowerSeries.mul_invOfUnit _ _ (by rw [Units.val_one]; exact hφ), map_one]
    calc MvPowerSeries.map f (φ.invOfUnit 1)
        = MvPowerSeries.map f (φ.invOfUnit 1) * (MvPowerSeries.map f φ * (MvPowerSeries.map f φ).invOfUnit 1) := by
          rw [h1, mul_one]
      _ = (MvPowerSeries.map f φ * MvPowerSeries.map f (φ.invOfUnit 1)) * (MvPowerSeries.map f φ).invOfUnit 1 := by
          ring
      _ = (MvPowerSeries.map f φ).invOfUnit 1 := by rw [h2, one_mul]

  have hW1 : (W.map f).fgW₁ = MvPowerSeries.map f W.fgW₁ := by
    unfold WeierstrassCurve.fgW₁
    rw [hW, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), MvPowerSeries.map_X]
  have hSl : (W.map f).fgSlope = MvPowerSeries.map f W.fgSlope := by
    ext d
    rw [MvPowerSeries.coeff_map]
    show PowerSeries.coeff (d 0 + d 1 + 1) (W.map f).formalW = f (PowerSeries.coeff (d 0 + d 1 + 1) W.formalW)
    rw [hW, PowerSeries.coeff_map]
  have hNu : (W.map f).fgNu = MvPowerSeries.map f W.fgNu := by
    unfold WeierstrassCurve.fgNu
    rw [hW1, hSl, map_sub, map_mul, MvPowerSeries.map_X]
  have hDen : (W.map f).fgZ3Denom = MvPowerSeries.map f W.fgZ3Denom := by
    unfold WeierstrassCurve.fgZ3Denom
    simp only [map_add, map_mul, map_pow, map_one, MvPowerSeries.map_C, hSl, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  have hNum : (W.map f).fgZ3NumFixed = MvPowerSeries.map f W.fgZ3NumFixed := by
    unfold WeierstrassCurve.fgZ3NumFixed
    simp only [map_add, map_mul, map_pow, map_neg, MvPowerSeries.map_C, hSl, hNu, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_ofNat]
  have hDen1 : MvPowerSeries.constantCoeff W.fgZ3Denom = 1 := by
    unfold WeierstrassCurve.fgZ3Denom
    simp [W.constantCoeff_fgSlope]
  have hZ3 : (W.map f).fgZ3Fixed = MvPowerSeries.map f W.fgZ3Fixed := by
    unfold WeierstrassCurve.fgZ3Fixed
    rw [hNum, hDen, ← hinvM _ hDen1, map_add, map_sub, map_neg, map_mul, MvPowerSeries.map_X, MvPowerSeries.map_X]
  have hID1 : PowerSeries.constantCoeff W.fgInvDenom = 1 := by
    unfold WeierstrassCurve.fgInvDenom
    simp [W.constantCoeff_formalW]
  have hID : (W.map f).fgInvDenom = PowerSeries.map f W.fgInvDenom := by
    unfold WeierstrassCurve.fgInvDenom
    simp only [map_sub, map_mul, map_one, PowerSeries.map_C, PowerSeries.map_X, hW, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃]
  have hInv : (W.map f).fgInv = PowerSeries.map f W.fgInv := by
    unfold WeierstrassCurve.fgInv
    rw [hID, ← hinvP _ hID1, map_mul, map_neg, PowerSeries.map_X]

  unfold WeierstrassCurve.formalGroupLawFixed
  rw [hZ3, hInv, PowerSeries.map_subst W.hasSubst_fgZ3Fixed]

end S_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
end P2MW
export P2MW.S_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map (solution)
