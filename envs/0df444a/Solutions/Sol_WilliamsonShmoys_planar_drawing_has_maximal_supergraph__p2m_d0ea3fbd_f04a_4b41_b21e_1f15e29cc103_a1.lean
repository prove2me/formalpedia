-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:57:50.528035+00:00
-- url     : https://prove2.me/submissions/bfe784d1-8c79-4a97-bc70-8d39d665885a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

/-- Every drawable graph on a fixed finite vertex type is contained in a maximal drawable graph. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let S : Type := {K : SimpleGraph V // G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hS : Nonempty S := ⟨⟨G, le_rfl, hDraw⟩⟩
  let f : S → ℕ := fun K => K.1.edgeFinset.card
  obtain ⟨H, hHmem, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset S) f
      (Finset.univ_nonempty_iff.mpr hS)
  refine ⟨H.1, H.2.1, H.2.2, ?_⟩
  intro K hHK hKDraw
  let K' : S := ⟨K, le_trans H.2.1 hHK, hKDraw⟩
  have hK'mem : K' ∈ (Finset.univ : Finset S) := Finset.mem_univ K'
  have hcardmax : K'.1.edgeFinset.card ≤ H.1.edgeFinset.card := by
    exact hmax K' hK'mem
  have hsubset : H.1.edgeFinset ⊆ K'.1.edgeFinset :=
    (SimpleGraph.edgeFinset_subset_edgeFinset).2 hHK
  have hcardle : H.1.edgeFinset.card ≤ K'.1.edgeFinset.card :=
    Finset.card_le_card hsubset
  have hcardeq : H.1.edgeFinset.card = K'.1.edgeFinset.card :=
    Nat.le_antisymm hcardle hcardmax
  have hedgeeq : H.1.edgeFinset = K'.1.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  have hgraph : H.1 = K'.1 :=
    (SimpleGraph.edgeFinset_inj).1 hedgeeq
  exact hgraph.symm