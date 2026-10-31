-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_0c9ddbae_e05c_4655_8aee_21825ef9cfbc_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:02:31.485665+00:00
-- url     : https://prove2.me/submissions/59188f14-ef53-4e9a-b2f8-0b0afe5c95c6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open SimpleGraph

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ¬ ∃ N : SimpleGraph V, M.edgeSet ⊂ N.edgeSet ∧
        WilliamsonShmoys.HasPlanarDrawingOn N := by
  classical
  let p : SimpleGraph V → Prop :=
    fun G => L ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hp : ∃ G : SimpleGraph V, p G := ⟨L, le_rfl, hDraw⟩
  obtain ⟨M, hM, hmax⟩ :=
    Set.exists_max_image {G : SimpleGraph V | p G} (fun G => G.edgeFinset.card)
      (Set.toFinite _) hp
  rcases hM with ⟨hLM, hMD⟩
  refine ⟨M, edgeSet_subset_edgeSet.mpr hLM, hMD, ?_⟩
  rintro ⟨N, hMN, hND⟩
  have hMN' : M < N := edgeSet_ssubset_edgeSet.mp hMN
  have hedge : M.edgeFinset ⊂ N.edgeFinset := edgeFinset_ssubset_edgeFinset.mpr hMN'
  have hcard : M.edgeFinset.card < N.edgeFinset.card := Finset.card_lt_card hedge
  have hNmax : N.edgeFinset.card ≤ M.edgeFinset.card :=
    hmax N ⟨hLM.trans (le_of_lt hMN'), hND⟩
  exact (not_lt_of_ge hNmax) hcard