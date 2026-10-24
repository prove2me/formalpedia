-- Prove2me | solution 1 for SDC.density_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:47:24.814148+00:00
-- url     : https://prove2.me/submissions/b02239ed-68d6-4c7b-a610-c82763993a1b

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
theorem sdc89_homCount_le {V W : Type*} [Fintype V] [Fintype W] (F : SimpleGraph V) (G : SimpleGraph W) :
    homCount F G ≤ Fintype.card W ^ Fintype.card V := by
  classical
  unfold homCount
  rw [← Fintype.card_fun, ← Nat.card_eq_fintype_card]
  exact Finite.card_subtype_le _

theorem sdc89_two_edge_le {W : Type*} [Fintype W] (G : SimpleGraph W) :
    2 * edgeCard G ≤ Fintype.card W ^ 2 := by
  classical
  have h1 : edgeCard G = G.edgeFinset.card := by
    unfold edgeCard; rw [Nat.card_eq_fintype_card]; simp [SimpleGraph.edgeFinset]
  rw [h1, ← G.sum_degrees_eq_twice_card_edges]
  calc ∑ v, G.degree v ≤ ∑ _v : W, Fintype.card W :=
        Finset.sum_le_sum fun v _ => (G.degree_lt_card_verts v).le
    _ = Fintype.card W ^ 2 := by simp [sq]

theorem sdc89_homCount_mono {V W : Type*} (F : SimpleGraph V) (G G' : SimpleGraph W) [Finite W] [Finite V]
    (h : G ≤ G') : homCount F G ≤ homCount F G' := by
  unfold homCount
  refine Nat.card_le_card_of_injective (fun x => ⟨x.1, fun l r hlr => h (x.2 l r hlr)⟩) ?_
  intro x y hxy
  exact Subtype.ext (by simpa using congrArg Subtype.val hxy)

theorem solution {W : Type*} [Fintype W] [Nonempty W] (G : SimpleGraph W) :
    0 ≤ homDensity H G ∧
    homDensity H G ≤ 1 ∧
    0 ≤ edgeDensity G ∧
    edgeDensity G ≤ 1 ∧
    ∀ G' : SimpleGraph W, G ≤ G' → homCount H G ≤ homCount H G' := by
  have hm : (0 : ℝ) < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨?_, ?_, ?_, ?_, fun G' h => sdc89_homCount_mono H G G' h⟩
  · unfold homDensity; positivity
  · unfold homDensity
    rw [sdc89_card_pattern, Nat.card_eq_fintype_card, div_le_one (by positivity)]
    have := sdc89_homCount_le H G
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    exact_mod_cast this
  · unfold edgeDensity; positivity
  · unfold edgeDensity
    rw [Nat.card_eq_fintype_card, div_le_one (by positivity)]
    exact_mod_cast sdc89_two_edge_le G
