-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_window_finite
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T10:16:36.716884+00:00
-- url     : https://prove2.me/submissions/5d9e2bd0-23c0-4b6e-a12c-02e99706585d

import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
open Set

theorem solution (a b : ℝ) : (RHHighHeight.windowZeros a b).Finite := by
  have hc : IsCompact ((Icc (0:ℝ) 1) ×ℂ (Icc a b)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  apply hc.inter_riemannZetaZeros_finite.subset
  intro s hs
  refine ⟨?_,?_⟩
  · exact ⟨⟨hs.2.1.le,hs.2.2.1.le⟩,hs.2.2.2⟩
  · exact hs.1
