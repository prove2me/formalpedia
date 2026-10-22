-- Prove2me | solution 1 for TradingPostNSW.Leontief.theorem_4_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T17:11:31.175885+00:00
-- url     : https://prove2.me/submissions/d5d42835-b0de-42aa-a11e-d5af745588a1

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Theorems.Thm_TradingPostNSW_Leontief_theorem_4_7
import Theorems.Thm_TradingPostNSW_Leontief_theorem_4_8

open TradingPostNSW.Leontief

theorem solution {n m : ℕ} (I : Instance n m) (ε Δ : ℝ) (b : Fin n → Fin m → ℝ)
    (hI : Standing I) (hPC : PerfectCompetition I) (hε : 0 < ε) (hΔ : 0 < Δ)
    (hΔε : Δ < ε / (m : ℝ) ^ 2) (hΔm : Δ < 1 / (m : ℝ)) (hb : IsPNE I Δ b)
    (y : Fin n → Fin m → ℝ) (hy : Feasible I y) :
    NSW I y ≤ (1 + ε) * NSW I (tpAlloc Δ b) :=
  theorem_4_8 I ε (bidPrice b) (tpAlloc Δ b) hI hε
    (theorem_4_7 I ε Δ b hI hPC hε hΔ hΔε hΔm hb) y hy
