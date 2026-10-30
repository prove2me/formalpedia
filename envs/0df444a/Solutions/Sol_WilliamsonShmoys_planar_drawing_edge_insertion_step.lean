-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_insertion_step
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:39:11.401973+00:00
-- url     : https://prove2.me/submissions/9a543a59-701b-4892-89b2-8323f4a8899a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (L : SimpleGraph V),
        WilliamsonShmoys.HasPlanarDrawingOn L →
        ¬ L.Connected →
        ∃ M : SimpleGraph V,
          L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
            L.edgeSet.ncard < M.edgeSet.ncard) := by
  intro h
  have hdraw :
      WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph Empty) := by
    simp only [WilliamsonShmoys.HasPlanarDrawingOn]
    refine ⟨(fun x : Empty => x.elim), (fun u v t => u.elim), ?_⟩
    refine ⟨?_, ?_⟩
    · intro x y hxy
      cases x
    · refine ⟨?_, ?_⟩
      · intro u
        cases u
      · intro u
        cases u
  have hnc : ¬ (⊥ : SimpleGraph Empty).Connected := by
    intro hc
    rcases hc.nonempty with ⟨v⟩
    cases v
  obtain ⟨M, hle, hplanar, hcount⟩ :=
    h (V := Empty) (L := (⊥ : SimpleGraph Empty)) hdraw hnc
  have hM : M = (⊥ : SimpleGraph Empty) := by
    ext u v
    cases u
  rw [hM] at hcount
  have hzero : (⊥ : SimpleGraph Empty).edgeSet.ncard = 0 := by
    simp [SimpleGraph.edgeSet]
  rw [hzero] at hcount
  exact Nat.lt_irrefl 0 hcount
