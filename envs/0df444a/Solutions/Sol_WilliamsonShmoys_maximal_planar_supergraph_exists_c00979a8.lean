-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists_c00979a8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:01:26.377092+00:00
-- url     : https://prove2.me/submissions/25531987-e5a1-43c4-9375-a97ec9d61f44

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V => N <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun K => N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have hcandidates : candidates.Nonempty := by
    refine ⟨N, ?_⟩
    simp [candidates, hN]
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image candidates (fun G => G.edgeFinset.card) hcandidates
  have hK : N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K :=
    (Finset.mem_filter.mp hKmem).2
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  by_contra hne
  have hlt : K < L := lt_of_le_of_ne hKL (Ne.symm hne)
  have hcard : K.edgeFinset.card < L.edgeFinset.card := by
    exact Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have hLmem : L ∈ candidates := by
    simp [candidates, hK.1.trans hKL, hL]
  have hmax := hKmax L hLmem
  omega