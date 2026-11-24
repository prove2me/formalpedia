-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_residuePart_conv_7c24ca73e8b7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:21.303233+00:00
-- url     : https://prove2.me/submissions/379cb6fa-c7f8-40a0-8ced-dee5447488b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
theorem _root_.solution {F : PowerSeries ℤ} {r : ℝ} (hr : 0 < r) (hF : IntSeriesConv F r)
    {p : ℕ} (hp : 0 < p) (i : ℕ) : IntSeriesConv (residuePart F p i) (r ^ p) := by
  unfold IntSeriesConv at *
  have hinj : Function.Injective fun m : ℕ ↦ m * p + i := fun a b h ↦
    Nat.eq_of_mul_eq_mul_right hp (Nat.add_right_cancel h)
  have h1 := (hF.comp_injective hinj).mul_left ((r ^ i)⁻¹)
  refine h1.congr fun m ↦ ?_
  have hri : r ^ i ≠ 0 := pow_ne_zero _ hr.ne'
  simp only [Function.comp_apply, residuePart, coeff_mk]
  rw [pow_add, pow_mul']
  field_simp
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
