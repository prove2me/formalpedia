-- Prove2me | solution 1 for WilliamsonShmoys.exists_card_maximal_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:43:09.793994+00:00
-- url     : https://prove2.me/submissions/c943c3a7-9911-44d7-8f60-637ff6eeb074

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, K ≤ M → HasPlanarDrawingOn M →
        M.edgeSet.ncard ≤ L.edgeSet.ncard := by
  classical
  let S : Set (SimpleGraph V) :=
    {L | K ≤ L ∧ HasPlanarDrawingOn L}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨L, hL, hmax⟩ :=
    hSfinite.exists_maximalFor (fun G : SimpleGraph V => G.edgeSet.ncard) S hSnonempty
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hKM hM
  have hMS : M ∈ S := ⟨hKM, hM⟩
  by_contra h
  have hLM : L.edgeSet.ncard ≤ M.edgeSet.ncard :=
    Nat.le_of_lt (Nat.lt_of_not_ge h)
  have hML : M.edgeSet.ncard ≤ L.edgeSet.ncard := hmax hMS hLM
  exact h hML