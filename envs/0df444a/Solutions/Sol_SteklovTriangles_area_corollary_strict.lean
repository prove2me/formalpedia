-- Prove2me | solution 1 for SteklovTriangles.area_corollary_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:51:01.939569+00:00
-- url     : https://prove2.me/submissions/31c75f66-d298-40f2-9569-f552acc8138c

import Mathlib
import Definitions.Def_SteklovTriangles_AreaCorollary

set_option autoImplicit false
open SteklovTriangles
namespace SteklovTriangles
theorem _root_.solution (σ L A S k : ℝ) (hσ : 0 ≤ σ) (hL : 0 < L) (hk : 0 < k)
    (hper : σ * L < S) (hiso : A ≤ k * L ^ 2) : σ * Real.sqrt A < S * Real.sqrt k := by
  have h1 : Real.sqrt A ≤ Real.sqrt k * L := by
    rw [show Real.sqrt k * L = Real.sqrt (k * L ^ 2) by
      rw [Real.sqrt_mul hk.le, Real.sqrt_sq hL.le]]
    exact Real.sqrt_le_sqrt hiso
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  calc σ * Real.sqrt A ≤ σ * (Real.sqrt k * L) := mul_le_mul_of_nonneg_left h1 hσ
    _ = (σ * L) * Real.sqrt k := by ring
    _ < S * Real.sqrt k := mul_lt_mul_of_pos_right hper hsk
end SteklovTriangles
