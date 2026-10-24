-- Prove2me | solution 1 for SDC.witness_inequality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:47:10.018005+00:00
-- url     : https://prove2.me/submissions/0d03ac5e-55f6-40f7-a423-73a0f015277b

import Mathlib
import Definitions.Def_SDC_graphs
import Definitions.Def_SDC_density
open SDC

theorem sdc89_card_pattern : Nat.card PatternVertex = 35 := by
  simp [Nat.card_sum]

theorem solution {W : Type*} [Fintype W] [Nonempty W] (G : SimpleGraph W) :
    homDensity H G < (edgeDensity G) ^ 66 ↔
      homCount H G * (Fintype.card W) ^ 132 <
        (2 * edgeCard G) ^ 66 * (Fintype.card W) ^ 35 := by
  unfold homDensity edgeDensity
  rw [sdc89_card_pattern, Nat.card_eq_fintype_card]
  have hm : (0 : ℝ) < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_pow, ← pow_mul, div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num
  constructor <;> intro h <;> exact_mod_cast h
