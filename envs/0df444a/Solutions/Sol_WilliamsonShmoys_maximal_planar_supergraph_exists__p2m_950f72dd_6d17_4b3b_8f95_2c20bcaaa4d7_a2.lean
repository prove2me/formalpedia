-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_950f72dd_6d17_4b3b_8f95_2c20bcaaa4d7_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:11:08.873806+00:00
-- url     : https://prove2.me/submissions/0fd36545-9353-4cd0-bf66-4864abb7f73c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun H => G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H
  have hcandidates : candidates.Nonempty := by
    refine ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ G, le_rfl, hG⟩⟩
  obtain ⟨H, hHmem, hHmax⟩ :=
    Finset.exists_max_image candidates (fun H => H.edgeFinset.card) hcandidates
  have hHprops := (Finset.mem_filter.mp hHmem).2
  refine ⟨H, hHprops.1, hHprops.2, ?_⟩
  intro K hHK hKplanar
  have hGK : G ≤ K := le_trans hHprops.1 hHK
  have hKmem : K ∈ candidates := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ K, hGK, hKplanar⟩
  by_contra hKH
  have hsub : H.edgeFinset ⊆ K.edgeFinset := SimpleGraph.edgeFinset_mono hHK
  have hrev : ¬ K.edgeFinset ⊆ H.edgeFinset := by
    intro hrev
    apply hKH
    have heq : H.edgeFinset = K.edgeFinset := Finset.Subset.antisymm hsub hrev
    have hEq : H = K := SimpleGraph.edgeFinset_inj.mp heq
    simpa [hEq] using (le_rfl : H ≤ H)
  have hcard : H.edgeFinset.card < K.edgeFinset.card :=
    Finset.card_lt_card ⟨hsub, hrev⟩
  exact (not_lt_of_ge (hHmax K hKmem)) hcard
