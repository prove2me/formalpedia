-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_to_planarMapDataExtension__p2m_9d34f080_ed68_445b_bb08_ad40d7fc216e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:51:43.206642+00:00
-- url     : https://prove2.me/submissions/a981627b-611d-41e3-8de4-a5382e87a46b

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_connected_supergraph__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
import Theorems.Thm_WilliamsonShmoys_face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (hK : DecidableRel K.Adj),
      (∀ ⦃u v : V⦄, J.Adj u v → K.Adj u v) ∧
      Nonempty (@PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3 V (inferInstance) K hK) := by
  classical
  obtain ⟨K, hJK, hKconn, hKdraw⟩ :=
    WilliamsonShmoys.drawable_connected_supergraph__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
      J hJ hcard
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨F, instF, length, heuler, hdegree, hsum⟩ :=
    WilliamsonShmoys.face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5
      K hKdraw hKconn hcard
  letI : Fintype F := instF
  have hedge : K.edgeSet.ncard = K.edgeFinset.card := by
    exact Set.ncard_eq_toFinset_card' K.edgeSet
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  refine ⟨K, Classical.decRel K.Adj, ?_, ?_⟩
  · intro u v huv
    exact hJK huv
  · refine ⟨{
      faceCount := Fintype.card F
      euler := ?_
      faceDegree := fun i => length (e i)
      sum_faceDegree := ?_
      faceDegree_ge_three := ?_ }⟩
    · simpa [hedge] using heuler
    · calc
        (∑ i : Fin (Fintype.card F), length (e i)) = ∑ f : F, length f :=
          Equiv.sum_comp e length
        _ = 2 * K.edgeFinset.card := by simpa only [hedge] using hsum
    · intro i
      exact hdegree (e i)
