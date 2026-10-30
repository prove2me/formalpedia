-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_4d6b09f4_cc64_4c42_8df1_4b93fc74bb58_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:17.826+00:00
-- url     : https://prove2.me/submissions/d355109a-0e62-412a-9a4f-fa79789efc76

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ K : SimpleGraph V, U ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | U ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hSfinite : S.Finite :=
    Set.Finite.subset Set.finite_univ (by
      intro K hK
      exact Set.mem_univ K)
  have hUne : U ∈ S := ⟨le_rfl, hU⟩
  obtain ⟨K, hK, hKmax⟩ :=
    Set.exists_max_image S (fun G : SimpleGraph V => G.edgeFinset.card)
      hSfinite ⟨U, hUne⟩
  rcases hK with ⟨hUK, hKplanar⟩
  refine ⟨K, hUK, hKplanar, ?_⟩
  intro L hKL hLplanar
  have hKLsubset : K.edgeFinset ⊆ L.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mpr hKL
  have hKLcard : K.edgeFinset.card ≤ L.edgeFinset.card :=
    Finset.card_le_card hKLsubset
  have hLKcard : L.edgeFinset.card ≤ K.edgeFinset.card :=
    hKmax L ⟨hUK.trans hKL, hLplanar⟩
  have hEdges : K.edgeFinset = L.edgeFinset :=
    Finset.eq_of_subset_of_card_le hKLsubset hLKcard
  have hEq : K = L := SimpleGraph.edgeFinset_inj.mp hEdges
  subst L
  exact le_rfl