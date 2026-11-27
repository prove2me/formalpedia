-- Prove2me | solution 1 for PLCMarkets.ExactCover.Supplement.lemma_6_3_total_demand_bound
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:39.592461+00:00
-- url     : https://prove2.me/submissions/16ee48cc-75e9-4544-b1d2-39e57a82022c

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_Supplement_FixedPointCell

open PLCMarkets
open PLCMarkets.ExactCover
open PLCMarkets.ExactCover.Supplement

open PLCMarkets.ExactCover

theorem solution {n g : ℕ} (M : ADMarket (Fin n) (Fin g))
    (hsupply : ∀ j, M.supply j = 1) (m : ℕ) (C : FixedPointCell M (mesh m)) :
    (∀ a j, totalDemand (C.vertex a).2 j ≤ 1 + 4 * n * g * mesh m) ∧
      ∀ j, totalDemand C.xStar j ≤ 1 + 4 * n * g * mesh m := by
        have hδ : 0 ≤ mesh m := by unfold mesh; positivity
        have avg_le : ∀ (f : Fin C.k → ℝ) (c : ℝ), (∀ a, f a ≤ c) → ∑ a, C.weight a * f a ≤ c := by
          intro f c hf
          calc ∑ a, C.weight a * f a ≤ ∑ a, C.weight a * c :=
                Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hf a) (C.weight_nonneg a)
            _ = c := by rw [← Finset.sum_mul, C.weight_sum, one_mul]
        have le_avg : ∀ (f : Fin C.k → ℝ) (c : ℝ), (∀ a, c ≤ f a) → c ≤ ∑ a, C.weight a * f a := by
          intro f c hf
          calc c = ∑ a, C.weight a * c := by rw [← Finset.sum_mul, C.weight_sum, one_mul]
            _ ≤ ∑ a, C.weight a * f a :=
                Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hf a) (C.weight_nonneg a)
        have cost_eq : ∀ (p : Fin g → ℝ) (x : Fin n → Fin g → ℝ),
            allocationCost p x = ∑ j, p j * totalDemand x j := by
          intro p x
          simp only [allocationCost, totalDemand, Finset.mul_sum]
          exact Finset.sum_comm
        have adjP : ∀ a b j, |(C.vertex a).1 j - (C.vertex b).1 j| ≤ (mesh m) := by
          intro a b j
          rcases (C.vertex_adjacent a b).1 j with h | h
          · rw [h, sub_self, abs_zero]; exact hδ
          · exact h.le
        have adjX : ∀ a b j, totalDemand (C.vertex a).2 j ≤ totalDemand (C.vertex b).2 j + n * (mesh m) := by
          intro a b j
          have : ∀ i, (C.vertex a).2 i j ≤ (C.vertex b).2 i j + (mesh m) := by
            intro i
            rcases (C.vertex_adjacent a b).2 i j with h | h
            · rw [h]; linarith
            · have := le_abs_self ((C.vertex a).2 i j - (C.vertex b).2 i j); linarith
          calc totalDemand (C.vertex a).2 j ≤ ∑ i : Fin n, ((C.vertex b).2 i j + (mesh m)) :=
                Finset.sum_le_sum fun i _ => this i
            _ = _ := by rw [Finset.sum_add_distrib]; simp [totalDemand, Finset.sum_const, nsmul_eq_mul]
        have budget : ∀ a, ∑ j, (C.vertex a).1 j * totalDemand (C.image a).2 j ≤ 1 := by
          intro a
          have h1 : ∀ i, ∑ j, (C.vertex a).1 j * (C.image a).2 i j ≤ M.income (C.vertex a).1 i :=
            fun i => ((C.image_mem a).2 i).2.1
          have h2 : ∑ j, (C.vertex a).1 j * totalDemand (C.image a).2 j
              = ∑ i, ∑ j, (C.vertex a).1 j * (C.image a).2 i j := by
            simp only [totalDemand, Finset.mul_sum]; exact Finset.sum_comm
          have h3 : ∑ i, M.income (C.vertex a).1 i = 1 := by
            simp only [ADMarket.income]
            rw [Finset.sum_comm]
            simp_rw [← Finset.mul_sum]
            have : ∀ j, ∑ i, (M.endow i j : ℝ) = 1 := fun j => hsupply j
            simp_rw [this, mul_one]; exact (C.vertex_mem a).1.2
          rw [h2, ← h3]; exact Finset.sum_le_sum fun i _ => h1 i
        have imgY : ∀ a j, 0 ≤ totalDemand (C.image a).2 j ∧
            totalDemand (C.image a).2 j ≤ n * (11/10) := by
          intro a j
          constructor
          · exact Finset.sum_nonneg fun i _ => (((C.image_mem a).2 i).1 j).1
          · calc totalDemand (C.image a).2 j ≤ ∑ i : Fin n, (11/10 : ℝ) :=
                  Finset.sum_le_sum fun i _ => (((C.image_mem a).2 i).1 j).2
              _ = _ := by simp
        have priceResp : ∀ a j0, totalDemand (C.vertex a).2 j0 ≤
            ∑ j, (C.image a).1 j * totalDemand (C.vertex a).2 j := by
          intro a j0
          have hs : ADMarket.InSimplex (fun j : Fin g => if j = j0 then (1:ℝ) else 0) := by
            refine ⟨fun j => by show 0 ≤ (if j = j0 then (1:ℝ) else 0); split_ifs <;> norm_num, by simp⟩
          have := (C.image_mem a).1.2 _ hs
          rw [cost_eq, cost_eq] at this
          simpa using this
        have Qsimp : ∀ a, ADMarket.InSimplex (C.image a).1 := fun a => (C.image_mem a).1.1
        have xs_img : ∀ j, totalDemand C.xStar j = ∑ a, C.weight a * totalDemand (C.image a).2 j := by
          intro j; simp only [totalDemand, C.xStar_image, Finset.mul_sum]; exact Finset.sum_comm
        have xs_vert : ∀ j, totalDemand C.xStar j = ∑ a, C.weight a * totalDemand (C.vertex a).2 j := by
          intro j; simp only [totalDemand, C.xStar_vertex, Finset.mul_sum]; exact Finset.sum_comm
        set S := ∑ j, C.pStar j * totalDemand C.xStar j with hS
        have S_upper : S ≤ 1 + n * (11/10) * g * (mesh m) := by
          have : S = ∑ a, C.weight a * ∑ j, C.pStar j * totalDemand (C.image a).2 j := by
            simp only [hS, xs_img, Finset.mul_sum]; rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
          rw [this]; apply avg_le; intro a
          have hp : ∀ j, C.pStar j ≤ (C.vertex a).1 j + (mesh m) := by
            intro j; rw [C.pStar_vertex]; apply avg_le; intro b
            have := adjP b a j
            have := le_abs_self ((C.vertex b).1 j - (C.vertex a).1 j); linarith
          calc ∑ j, C.pStar j * totalDemand (C.image a).2 j
                ≤ ∑ j, ((C.vertex a).1 j + (mesh m)) * totalDemand (C.image a).2 j :=
                Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hp j) (imgY a j).1
            _ = ∑ j, (C.vertex a).1 j * totalDemand (C.image a).2 j
                  + ∑ j, (mesh m) * totalDemand (C.image a).2 j := by
                rw [← Finset.sum_add_distrib]
                exact Finset.sum_congr rfl fun j _ => by ring
            _ ≤ 1 + ∑ j : Fin g, (mesh m) * (n * (11/10)) :=
                add_le_add (budget a)
                  (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (imgY a j).2 hδ)
            _ = _ := by simp; ring
        have S_lower : ∀ b j0, totalDemand (C.vertex b).2 j0 ≤ S + 2 * n * (mesh m) := by
          intro b j0
          have hSQ : S = ∑ a, C.weight a * ∑ j, (C.image a).1 j * totalDemand C.xStar j := by
            simp only [hS, C.pStar_image, Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
          have key : ∀ a, totalDemand (C.vertex b).2 j0 - 2 * n * (mesh m) ≤
              ∑ j, (C.image a).1 j * totalDemand C.xStar j := by
            intro a
            have hx : ∀ j, totalDemand (C.vertex a).2 j - n * (mesh m) ≤ totalDemand C.xStar j := by
              intro j; rw [xs_vert]; apply le_avg; intro c; have := adjX a c j; linarith
            have h1 := priceResp a j0
            have h2 := adjX b a j0
            have h3 : ∑ j, (C.image a).1 j * totalDemand (C.vertex a).2 j - n * (mesh m) ≤
                ∑ j, (C.image a).1 j * totalDemand C.xStar j := by
              calc _ = ∑ j, (C.image a).1 j * (totalDemand (C.vertex a).2 j - n * (mesh m)) := by
                      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (Qsimp a).2, one_mul]
                _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx j) ((Qsimp a).1 j)
            linarith
          have := le_avg _ _ key
          rw [hSQ]; linarith
        have vert : ∀ a j, totalDemand (C.vertex a).2 j ≤ 1 + 4 * n * g * (mesh m) := by
          intro a j
          have hg : (1:ℝ) ≤ g := by
            have := j.pos
            exact_mod_cast this
          have h1 := S_lower a j
          have hn : (0:ℝ) ≤ n := by positivity
          have hnd := mul_nonneg hn hδ
          nlinarith [mul_le_mul_of_nonneg_left hg hnd]
        refine ⟨vert, fun j => ?_⟩
        rw [xs_vert]; apply avg_le; intro a; exact vert a j
