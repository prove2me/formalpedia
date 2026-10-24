-- Prove2me | solution 1 for SDC.pattern_facts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:47:32.8915+00:00
-- url     : https://prove2.me/submissions/b20da5d7-34e7-4745-b0ed-ffc1a68cf5d3

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
instance sdc89_decAdj : DecidableRel H.Adj := fun a b => by
  cases a <;> cases b <;> simp only [H, incidence] <;> infer_instance

theorem sdc89_edge_card : H.edgeSet.ncard = 66 := by
  classical
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have h := H.sum_degrees_eq_twice_card_edges
  have h2 : ∑ v, H.degree v = 132 := by decide
  omega

theorem solution :
    H.IsBipartite ∧
    H.edgeSet.ncard = 66 ∧
    (∀ f : Fin 22, (faces f).card = 3) ∧
    ∀ p : Fin 13, ∃ f : Fin 22, p ∈ faces f := by
  refine ⟨?_, sdc89_edge_card, by decide, by decide⟩
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v.isLeft then (0 : Fin 2) else 1) ?_⟩
  intro a b hab
  cases a <;> cases b <;> simp_all [H, incidence]
