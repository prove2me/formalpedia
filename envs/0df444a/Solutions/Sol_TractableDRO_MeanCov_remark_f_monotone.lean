-- Prove2me | solution 1 for TractableDRO.MeanCov.remark_f_monotone
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:46:56.76525+00:00
-- url     : https://prove2.me/submissions/ec289c43-2931-481b-bec8-98923caad9dd

import Mathlib
import Definitions.Def_TractableDRO_MeanCov_Model

open Matrix

namespace TractableDRO.MeanCov

theorem remark_f_monotone {N : ℕ} (Sig : Matrix (Fin N) (Fin N) ℝ) (hSig : Sig.PosSemidef)
    (y : Fin N → ℝ) :
    Monotone (fun u : ℝ => u / 2 + Real.sqrt (u ^ 2 + y ⬝ᵥ Sig *ᵥ y) / 2) := by
  have hq : 0 ≤ y ⬝ᵥ Sig *ᵥ y := hSig.dotProduct_mulVec_nonneg y
  intro u v huv
  have hu : 0 ≤ u ^ 2 + y ⬝ᵥ Sig *ᵥ y := by positivity
  have hv : 0 ≤ v ^ 2 + y ⬝ᵥ Sig *ᵥ y := by positivity
  have hsu := Real.sqrt_nonneg (u ^ 2 + y ⬝ᵥ Sig *ᵥ y)
  have hsv := Real.sqrt_nonneg (v ^ 2 + y ⬝ᵥ Sig *ᵥ y)
  have heu := Real.sq_sqrt hu
  have hev := Real.sq_sqrt hv
  have hbound : 0 ≤ v + Real.sqrt (v ^ 2 + y ⬝ᵥ Sig *ᵥ y) := by
    nlinarith
  by_contra hn
  have hlt : Real.sqrt (v ^ 2 + y ⬝ᵥ Sig *ᵥ y) + (v-u) <
      Real.sqrt (u ^ 2 + y ⬝ᵥ Sig *ᵥ y) := by linarith
  have hsquare := (sq_lt_sq₀ (by positivity : 0 ≤ Real.sqrt (v ^ 2 + y ⬝ᵥ Sig *ᵥ y) + (v-u)) hsu).2 hlt
  nlinarith [mul_nonneg (sub_nonneg.mpr huv) hbound]


end TractableDRO.MeanCov

theorem solution {N : ℕ} (Sig : Matrix (Fin N) (Fin N) ℝ) (hSig : Sig.PosSemidef)
    (y : Fin N → ℝ) :
    Monotone (fun u : ℝ => u / 2 + Real.sqrt (u ^ 2 + y ⬝ᵥ Sig *ᵥ y) / 2) := TractableDRO.MeanCov.remark_f_monotone Sig hSig y

#print axioms solution
