-- Prove2me | solution 1 for WilliamsonShmoys.insert_edge_graph_exists__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:54:07.448523+00:00
-- url     : https://prove2.me/submissions/c1ce2371-0c0c-4d0d-b01d-3e6a3b6899e8

-- ID: e6252305-dd78-4cc5-acd9-da4b76f8d4e8 | NAME: WilliamsonShmoys.insert_edge_graph_exists__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a2 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (u v : V) (huv : u ≠ v) : ∃ G : SimpleGraph V, H ≤ G ∧ G.Adj u v ∧ ∀ x y, G.Adj x y ↔ H.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  let G : SimpleGraph V :=
    { Adj := fun x y => H.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)
      symm.symm := by
        rintro x y (h | h | h)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
        · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      loopless.irrefl := by
        intro x h
        rcases h with h | h | h
        · exact h.ne rfl
        · exact huv (h.1.symm.trans h.2)
        · exact huv (h.2.symm.trans h.1) }
  refine ⟨G, ?_, ?_, ?_⟩
  · intro x y h
    exact Or.inl h
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · intro x y
    rfl
