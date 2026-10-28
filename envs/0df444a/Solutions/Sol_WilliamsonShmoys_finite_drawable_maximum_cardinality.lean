-- Prove2me | solution 1 for WilliamsonShmoys.finite_drawable_maximum_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:12:07.463642+00:00
-- url     : https://prove2.me/submissions/120077f6-2fac-4610-bd23-f4e62c2a17f9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_mem_of_bounded_nat_set

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        H.edgeSet ⊆ L.edgeSet →
        HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  let S : Set Nat := {n | ∃ K : SimpleGraph V,
    H.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K ∧ K.edgeSet.ncard = n}
  have hS : S.Nonempty := by
    refine ⟨H.edgeSet.ncard, ?_⟩
    exact ⟨H, subset_rfl, hH, rfl⟩
  have hB : ∀ n ∈ S, n ≤ (Set.univ : Set (Sym2 V)).ncard := by
    intro n hn
    rcases hn with ⟨K, _, _, hKn⟩
    calc
      n = K.edgeSet.ncard := hKn.symm
      _ ≤ (Set.univ : Set (Sym2 V)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
  obtain ⟨m, hmS, hmMax⟩ :=
    WilliamsonShmoys.exists_maximal_mem_of_bounded_nat_set S
      (Set.univ : Set (Sym2 V)).ncard hS hB
  rcases hmS with ⟨K, hHK, hK, hKm⟩
  refine ⟨K, hHK, hK, ?_⟩
  intro L hHL hL
  have hLM : L.edgeSet.ncard ∈ S := ⟨L, hHL, hL, rfl⟩
  calc
    L.edgeSet.ncard ≤ m := hmMax (L.edgeSet.ncard) hLM
    _ = K.edgeSet.ncard := hKm.symm