-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:33:18.701994+00:00
-- url     : https://prove2.me/submissions/7e1f90db-c6fd-4dec-b8fb-564def4e45f8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun K : SimpleGraph V =>
      And (L <= K) (And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (forall K' : SimpleGraph V, K <= K' ->
          WilliamsonShmoys.HasPlanarDrawingOn K' -> K' = K)) := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | And (L <= K) (WilliamsonShmoys.HasPlanarDrawingOn K)}
  have hSfinite : S.Finite := Set.toFinite S
  obtain ⟨K, hKmem, hKmax⟩ :=
    Set.exists_max_image S (fun H : SimpleGraph V => H.edgeFinset.card)
      hSfinite ⟨L, by simp [S, hL]⟩
  have hKprops : And (L <= K) (WilliamsonShmoys.HasPlanarDrawingOn K) := by
    change K ∈ S at hKmem
    exact hKmem
  have hKL : L <= K := hKprops.1
  have hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K := hKprops.2
  refine ⟨K, hKL, hKplanar, ?_⟩
  intro K' hKK' hK'planar
  have hK'mem : K' ∈ S := by
    change And (L <= K') (WilliamsonShmoys.HasPlanarDrawingOn K')
    exact ⟨le_trans hKL hKK', hK'planar⟩
  by_contra hne
  have hlt : K < K' := lt_of_le_of_ne hKK' (Ne.symm hne)
  have hss : K.edgeFinset ⊂ K'.edgeFinset :=
    SimpleGraph.edgeFinset_strict_mono hlt
  have hcard : K.edgeFinset.card < K'.edgeFinset.card :=
    Finset.card_lt_card hss
  have hmaxcard := hKmax K' hK'mem
  omega