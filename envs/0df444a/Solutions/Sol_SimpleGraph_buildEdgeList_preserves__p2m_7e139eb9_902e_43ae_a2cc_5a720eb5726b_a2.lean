-- Prove2me | solution 1 for SimpleGraph.buildEdgeList_preserves__p2m_7e139eb9_902e_43ae_a2cc_5a720eb5726b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:25:46.501913+00:00
-- url     : https://prove2.me/submissions/7b62ec01-da18-4127-ab60-95a335e96a89

import Mathlib.Combinatorics.SimpleGraph.Operations

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hzero : P ⊥)
    (hadd : ∀ (K : SimpleGraph V), K ≤ G →
      ∀ u v : V, u < v → G.Adj u v → ¬ K.Adj u v →
      P K → P (K ⊔ SimpleGraph.edge u v)) :
    ∀ (H : SimpleGraph V), H ≤ G → P H →
    ∀ es : List (V × V),
      (∀ p, p ∈ es → p.1 < p.2 ∧ G.Adj p.1 p.2) →
      P (es.foldl (fun K p => K ⊔ SimpleGraph.edge p.1 p.2) H) := by
  intro H hHG hPH es
  induction es generalizing H with
  | nil =>
      simpa using hPH
  | cons p es ih =>
      intro hvalid
      have hp := hvalid p (by simp)
      obtain ⟨hlt, hadj⟩ := hp
      have hedge_le : SimpleGraph.edge p.1 p.2 ≤ G := by
        intro x y hxy
        rcases (SimpleGraph.edge_adj p.1 p.2 x y).mp hxy with ⟨hxy, _⟩
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadj
        · exact G.adj_symm hadj
      have hKG : H ⊔ SimpleGraph.edge p.1 p.2 ≤ G := sup_le hHG hedge_le
      have hPadd : P (H ⊔ SimpleGraph.edge p.1 p.2) := by
        by_cases hK : H.Adj p.1 p.2
        · rw [SimpleGraph.sup_edge_of_adj H hK]
          exact hPH
        · exact hadd H hHG p.1 p.2 hlt hadj hK hPH
      simpa [List.foldl] using
        (ih (H := H ⊔ SimpleGraph.edge p.1 p.2) hKG hPadd
          (fun q hq => hvalid q (by simp [hq])))