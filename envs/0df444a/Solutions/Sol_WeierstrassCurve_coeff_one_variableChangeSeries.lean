-- Prove2me | solution 1 for WeierstrassCurve.coeff_one_variableChangeSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/47c322dc-b76e-5e33-9a00-5f6b0af3d87f

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_coeff_one_variableChangeSeries

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    PowerSeries.coeff 1 (W.variableChangeSeries C) = (C.u : R) := by
  unfold WeierstrassCurve.variableChangeSeries
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (PowerSeries.C (C.u : R) * (PowerSeries.X - PowerSeries.C C.r * W.formalW)) *
      PowerSeries.coeff j ((W.variableChangeDenom C).invOfUnit 1)) 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply ((W.variableChangeDenom C).invOfUnit 1),
    PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one, mul_one]
  simp [PowerSeries.coeff_C_mul, W.constantCoeff_formalW, W.coeff_formalW_one, PowerSeries.coeff_X]

end S_WeierstrassCurve_coeff_one_variableChangeSeries
end P2MW
export P2MW.S_WeierstrassCurve_coeff_one_variableChangeSeries (solution)
