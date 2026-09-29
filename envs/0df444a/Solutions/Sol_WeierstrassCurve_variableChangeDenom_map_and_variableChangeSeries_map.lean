-- Prove2me | solution 1 for WeierstrassCurve.variableChangeDenom_map_and_variableChangeSeries_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5deb6f2e-233d-5f47-bd65-9479d2bfdc61

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_variableChangeDenom_map_and_variableChangeSeries_map

set_option autoImplicit false

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)
    (f : R →+* S) :
    (W.map f).variableChangeDenom (C.map f) = PowerSeries.map f (W.variableChangeDenom C) ∧
      (W.map f).variableChangeSeries (C.map f) = PowerSeries.map f (W.variableChangeSeries C) := by

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

  have hD : (W.map f).variableChangeDenom (C.map f) = PowerSeries.map f (W.variableChangeDenom C) := by
    unfold WeierstrassCurve.variableChangeDenom
    simp only [map_add, map_mul, map_sub, map_one, PowerSeries.map_C, PowerSeries.map_X, hW,
      WeierstrassCurve.VariableChange.map_r, WeierstrassCurve.VariableChange.map_s,
      WeierstrassCurve.VariableChange.map_t]
  refine ⟨hD, ?_⟩

  have hc1 : PowerSeries.constantCoeff (W.variableChangeDenom C) = ((1 : Rˣ) : R) := by
    rw [Units.val_one]; exact W.constantCoeff_variableChangeDenom C
  have hc1' : PowerSeries.constantCoeff ((W.map f).variableChangeDenom (C.map f)) = ((1 : Sˣ) : S) := by
    rw [Units.val_one]; exact (W.map f).constantCoeff_variableChangeDenom (C.map f)
  have hinv : ((W.map f).variableChangeDenom (C.map f)).invOfUnit 1 =
      PowerSeries.map f ((W.variableChangeDenom C).invOfUnit 1) := by
    have h1 : (W.map f).variableChangeDenom (C.map f) * ((W.map f).variableChangeDenom (C.map f)).invOfUnit 1 = 1 :=
      PowerSeries.mul_invOfUnit _ _ hc1'
    have h2 : (W.map f).variableChangeDenom (C.map f) * PowerSeries.map f ((W.variableChangeDenom C).invOfUnit 1) = 1 := by
      rw [hD, ← map_mul, PowerSeries.mul_invOfUnit _ _ hc1, map_one]
    calc ((W.map f).variableChangeDenom (C.map f)).invOfUnit 1
        = ((W.map f).variableChangeDenom (C.map f)).invOfUnit 1 *
            ((W.map f).variableChangeDenom (C.map f) * PowerSeries.map f ((W.variableChangeDenom C).invOfUnit 1)) := by
          rw [h2, mul_one]
      _ = ((W.map f).variableChangeDenom (C.map f) * ((W.map f).variableChangeDenom (C.map f)).invOfUnit 1) *
            PowerSeries.map f ((W.variableChangeDenom C).invOfUnit 1) := by ring
      _ = PowerSeries.map f ((W.variableChangeDenom C).invOfUnit 1) := by rw [h1, one_mul]
  unfold WeierstrassCurve.variableChangeSeries
  rw [hinv, map_mul, map_mul, map_sub, PowerSeries.map_C, PowerSeries.map_X, map_mul, PowerSeries.map_C, hW,
    WeierstrassCurve.VariableChange.map_u, Units.coe_map, WeierstrassCurve.VariableChange.map_r]
  rfl

end S_WeierstrassCurve_variableChangeDenom_map_and_variableChangeSeries_map
end P2MW
export P2MW.S_WeierstrassCurve_variableChangeDenom_map_and_variableChangeSeries_map (solution)
