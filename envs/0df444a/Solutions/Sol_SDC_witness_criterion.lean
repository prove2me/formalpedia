-- Prove2me | solution 1 for SDC.witness_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:47:17.056727+00:00
-- url     : https://prove2.me/submissions/b14717ae-1248-4537-ba83-7bd730968190

import Mathlib
import Definitions.Def_SDC_graphs
import Definitions.Def_SDC_density
open SDC

theorem sdc89_card_pattern : Nat.card PatternVertex = 35 := by
  simp

theorem sdc89_wi {W : Type*} [Fintype W] [Nonempty W] (G : SimpleGraph W) :
    homDensity H G < (edgeDensity G) ^ 66 ↔
      homCount H G * (Fintype.card W) ^ 132 <
        (2 * edgeCard G) ^ 66 * (Fintype.card W) ^ 35 := by
  unfold homDensity edgeDensity
  rw [sdc89_card_pattern, Nat.card_eq_fintype_card]
  have hm : (0 : ℝ) < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_pow, ← pow_mul, div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num
  constructor <;> intro h <;> exact_mod_cast h
theorem solution :
    (∃ size : ℕ, 0 < size ∧ ∃ host : SimpleGraph (Fin size),
        (∃ left right, host.Adj left right) ∧
        homDensity H host < (edgeDensity host) ^ 66) ↔
      (∃ size : ℕ, 0 < size ∧ ∃ host : SimpleGraph (Fin size),
        (∃ left right, host.Adj left right) ∧
        homCount H host * size ^ 132 < (2 * edgeCard host) ^ 66 * size ^ 35) := by
  constructor
  · rintro ⟨n, hn, G, he, h⟩
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine ⟨n, hn, G, he, ?_⟩
    simpa using (sdc89_wi G).1 h
  · rintro ⟨n, hn, G, he, h⟩
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine ⟨n, hn, G, he, ?_⟩
    exact (sdc89_wi G).2 (by simpa using h)
