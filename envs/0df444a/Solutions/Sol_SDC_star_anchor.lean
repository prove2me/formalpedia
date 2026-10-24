-- Prove2me | solution 1 for SDC.star_anchor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:50:12.854692+00:00
-- url     : https://prove2.me/submissions/7b25134d-af44-4418-b76c-f5adb1c65cd9

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

theorem sdc89_star_count (t : ℕ) {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    homCount (starGraph t) G = ∑ v : W, G.degree v ^ t := by
  rw [sdc89_hom_bip (starGraph t) (fun _ _ => True) (fun _ _ => Iff.rfl) (fun _ _ h => h)
    (fun _ _ h => h) G]
  rw [← (Equiv.funUnique (Fin 1) W).symm.sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  have : (⋂ a : Fin 1, ⋂ (_ : True), G.neighborSet ((Equiv.funUnique (Fin 1) W).symm v a))
      = G.neighborSet v := by
    ext x; simp
  rw [this, ← G.card_neighborFinset_eq_degree, Set.ncard_eq_toFinset_card']
  congr 1

theorem solution (t : ℕ) {W : Type*} [Fintype W] [Nonempty W] (G : SimpleGraph W) :
    (edgeDensity G) ^ t ≤ homDensity (starGraph t) G := by
  classical
  have hm : (0 : ℝ) < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  set m : ℝ := (Fintype.card W : ℝ) with hmdef
  have he : (2 * edgeCard G : ℝ) = ∑ v, (G.degree v : ℝ) := by
    have h1 : edgeCard G = G.edgeFinset.card := by
      unfold edgeCard; rw [Nat.card_eq_fintype_card]; simp [SimpleGraph.edgeFinset]
    rw [h1]; exact_mod_cast G.sum_degrees_eq_twice_card_edges.symm
  have hed : edgeDensity G = ∑ v, (1 / m) * ((G.degree v : ℝ) / m) := by
    unfold edgeDensity; rw [Nat.card_eq_fintype_card, he, Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hmdef]; field_simp
  have hhd : homDensity (starGraph t) G = ∑ v, (1 / m) * ((G.degree v : ℝ) / m) ^ t := by
    unfold homDensity
    rw [sdc89_star_count, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_sum, Nat.cast_pow]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hmdef, div_pow]; field_simp; ring
  rw [hed, hhd]
  apply Real.pow_arith_mean_le_arith_mean_pow
  · intro i _; positivity
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rw [← hmdef]; field_simp
  · intro i _; positivity
