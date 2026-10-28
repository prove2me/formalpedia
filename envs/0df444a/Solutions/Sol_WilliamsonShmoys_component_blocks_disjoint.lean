-- Prove2me | solution 1 for WilliamsonShmoys.component_blocks_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:15:27.904918+00:00
-- url     : https://prove2.me/submissions/ba3ba5af-c4a2-40d5-8869-dfa015f95e93

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Reachable] :
    ∀ C ∈ Finset.univ.image (fun v : V => Finset.univ.filter (fun w : V => G.Reachable v w)),
      ∀ D ∈ Finset.univ.image (fun v : V => Finset.univ.filter (fun w : V => G.Reachable v w)),
        C ≠ D → Disjoint C D := by
  intro C hC D hD hne
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hC hD
  obtain ⟨u, rfl⟩ := hC
  obtain ⟨v, rfl⟩ := hD
  rw [Finset.disjoint_left]
  intro w hu hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  apply hne
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => hv.trans (hu.symm.trans h), fun h => hu.trans (hv.symm.trans h)⟩
