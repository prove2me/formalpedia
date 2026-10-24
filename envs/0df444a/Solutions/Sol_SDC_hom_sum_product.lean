-- Prove2me | solution 1 for SDC.hom_sum_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:48:44.731279+00:00
-- url     : https://prove2.me/submissions/085db2cc-19ed-44d4-89fb-0372df9ebd0f

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
theorem sdc89_hom_bip {α β W : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Fintype W]
    (F : SimpleGraph (α ⊕ β)) (R : α → β → Prop)
    (h1 : ∀ a b, F.Adj (Sum.inl a) (Sum.inr b) ↔ R a b)
    (h2 : ∀ a a', ¬ F.Adj (Sum.inl a) (Sum.inl a'))
    (h3 : ∀ b b', ¬ F.Adj (Sum.inr b) (Sum.inr b')) (G : SimpleGraph W) :
    homCount F G = ∑ φ : α → W, ∏ b : β,
      (⋂ a, ⋂ (_ : R a b), G.neighborSet (φ a)).ncard := by
  classical
  let e : {hom : α ⊕ β → W // ∀ l r, F.Adj l r → G.Adj (hom l) (hom r)} ≃
      Σ φ : α → W, ∀ b : β, ↥(⋂ a, ⋂ (_ : R a b), G.neighborSet (φ a)) :=
    { toFun := fun h => ⟨h.1 ∘ Sum.inl, fun b => ⟨h.1 (Sum.inr b), by
          simp only [Set.mem_iInter, SimpleGraph.mem_neighborSet, Function.comp]
          intro a hab
          exact h.2 _ _ ((h1 a b).2 hab)⟩⟩
      invFun := fun x => ⟨Sum.elim x.1 (fun b => (x.2 b).1), by
          intro l r hlr
          rcases l with a | b <;> rcases r with a' | b'
          · exact absurd hlr (h2 a a')
          · have hm := (x.2 b').2
            simp only [Set.mem_iInter, SimpleGraph.mem_neighborSet] at hm
            exact hm a ((h1 a b').1 hlr)
          · have hm := (x.2 b).2
            simp only [Set.mem_iInter, SimpleGraph.mem_neighborSet] at hm
            exact (hm a' ((h1 a' b).1 hlr.symm)).symm
          · exact absurd hlr (h3 b b')⟩
      left_inv := fun h => by
        apply Subtype.ext; funext x; rcases x with a | b <;> rfl
      right_inv := fun x => rfl }
  unfold homCount
  rw [Nat.card_congr e, Nat.card_sigma]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Nat.card_pi]
  refine Finset.prod_congr rfl fun b _ => ?_
  exact Nat.card_coe_set_eq _

theorem solution {W : Type*} [Fintype W] (G : SimpleGraph W) :
    homCount H G =
      ∑ φ : (Fin 13 → W), ∏ f : Fin 22,
        (⋂ p ∈ faces f, G.neighborSet (φ p)).ncard :=
  sdc89_hom_bip H (fun p f => p ∈ faces f) (fun _ _ => Iff.rfl) (fun _ _ h => h) (fun _ _ h => h) G
