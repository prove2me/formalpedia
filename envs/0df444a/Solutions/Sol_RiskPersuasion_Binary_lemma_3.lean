-- Prove2me | solution 1 for RiskPersuasion.Binary.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:03:16.989205+00:00
-- url     : https://prove2.me/submissions/c3af3826-6da5-4293-b1bc-7d30d3ad28d6

import Mathlib
import Definitions.Def_RiskPersuasion_Binary_Model

set_option autoImplicit false

open RiskPersuasion.Binary

theorem solution {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : (Ω → ℝ) → Fin 2 → ℝ)
    (hq : QuasiconvexOn ℝ (stdSimplex ℝ Ω) (ρhat ρ)) :
    Assumption2 ρ := by
  exact hq.convex_lt 0
