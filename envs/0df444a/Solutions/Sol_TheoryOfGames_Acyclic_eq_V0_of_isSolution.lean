-- Prove2me | solution 1 for TheoryOfGames.Acyclic.eq_V0_of_isSolution
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T15:27:19.684429+00:00
-- url     : https://prove2.me/submissions/ae950377-3d76-4ddf-adfd-13b7fed96947

import Theorems.Thm_TheoryOfGames_Acyclic_V0_isSolution

open TheoryOfGames.Acyclic

private theorem mem_solution {α : Type*} {D V : Set α} {S : α → α → Prop}
    (hV : IsSolution D S V) (y : α) :
    y ∈ V ↔ y ∈ D ∧ ∀ x ∈ V, ¬ S x y :=
  Set.ext_iff.mp hV y

-- The book's (65:4): every maximum selected at any stage lies in every solution.
private theorem stageB_subset_solution {α : Type*} (D : Set α) (S : α → α → Prop)
    (V : Set α) (hV : IsSolution D S V) (k : ℕ) : stageB D S k ⊆ V := by
  have hVD : V ⊆ D := fun y hy => ((mem_solution hV y).mp hy).1
  have hAD : ∀ j, stageA D S j ⊆ D := by
    intro j
    induction j with
    | zero => exact Set.Subset.rfl
    | succ j ih => exact fun y hy => ih hy.1.1
  have maximal_mem (j : ℕ)
      (hc : ∀ x ∈ V, ∀ y ∈ stageA D S j, S x y → x ∈ stageA D S j) :
      stageB D S j ⊆ V := by
    intro y hy
    apply (mem_solution hV y).mpr
    refine ⟨hAD j hy.1, ?_⟩
    intro x hx hxy
    exact hy.2 x (hc x hx y hy.1 hxy) hxy
  -- A dominator in V of a surviving element must itself survive.
  have closed : ∀ j, ∀ x ∈ V, ∀ y ∈ stageA D S j,
      S x y → x ∈ stageA D S j := by
    intro j
    induction j with
    | zero =>
      intro x hx y hy hxy
      exact hVD hx
    | succ j ih =>
      have hB : stageB D S j ⊆ V := maximal_mem j ih
      intro x hx y hy hxy
      change (y ∈ stageA D S j ∧ y ∉ maxima (stageA D S j) S) ∧
        ¬ (y ∈ stageA D S j ∧ ∃ b ∈ maxima (stageA D S j) S, S b y) at hy
      have hxA := ih x hx y hy.1.1 hxy
      change (x ∈ stageA D S j ∧ x ∉ maxima (stageA D S j) S) ∧
        ¬ (x ∈ stageA D S j ∧ ∃ b ∈ maxima (stageA D S j) S, S b x)
      refine ⟨⟨hxA, fun hxB => hy.2 ⟨hy.1.1, x, hxB, hxy⟩⟩, ?_⟩
      rintro ⟨_, b, hb, hbx⟩
      exact ((mem_solution hV x).mp hx).2 b (hB hb) hbx
  exact maximal_mem k (closed k)

theorem solution {α : Type*} (D : Set α) (S : α → α → Prop)
    (hD : D.Finite) (hS : IsAcyclic D S) (V : Set α) (hV : IsSolution D S V) :
    V = V0 D S := by
  have h0 := V0_isSolution D S hD hS
  have h0V : V0 D S ⊆ V := by
    intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    exact stageB_subset_solution D S V hV k hk
  apply Set.Subset.antisymm ?_ h0V
  intro y hy
  apply (mem_solution h0 y).mpr
  have hy' := (mem_solution hV y).mp hy
  exact ⟨hy'.1, fun x hx => hy'.2 x (h0V hx)⟩
