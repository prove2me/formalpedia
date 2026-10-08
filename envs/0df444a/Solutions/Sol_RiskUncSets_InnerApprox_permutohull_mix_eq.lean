-- Prove2me | solution 1 for RiskUncSets.InnerApprox.permutohull_mix_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:06:20.200019+00:00
-- url     : https://prove2.me/submissions/c5d9d0b4-fc80-419f-a4c8-f12e8a5539d9

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
noncomputable section

open RiskUncSets.InnerApprox in
theorem solution {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (lam : ℝ) :
    permutohull (mix q lam) a = (fun w => sampleMean a + lam • w) '' piTilde q a := by
  unfold piTilde
  rw [Set.image_image]
  have hf : (fun w => sampleMean a + lam • (w - sampleMean a)) =
      ⇑(AffineMap.homothety (sampleMean a) lam) := by
    funext w
    simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm]
  rw [hf]
  unfold permutohull
  rw [AffineMap.image_convexHull, ← Set.range_comp]
  congr 2
  funext σ
  simp only [Function.comp_apply, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, mix,
    sampleMean, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
  module
