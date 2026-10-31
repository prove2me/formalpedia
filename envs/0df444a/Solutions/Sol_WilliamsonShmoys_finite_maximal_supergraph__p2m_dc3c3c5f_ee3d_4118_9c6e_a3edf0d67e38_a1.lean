-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph__p2m_dc3c3c5f_ee3d_4118_9c6e_a3edf0d67e38_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:37:55.866449+00:00
-- url     : https://prove2.me/submissions/83937547-138a-452f-a5cd-c98558d58acc

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (Z : SimpleGraph V) (hZ : P Z) :
    ∃ W : SimpleGraph V, Z ≤ W ∧ P W ∧
      ∀ X : SimpleGraph V, W ≤ X → P X → X ≤ W := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun G => Z ≤ G ∧ P G
  have hS : S.Nonempty := by
    refine ⟨Z, ?_⟩
    simp [S, hZ]
  obtain ⟨W, hWmem, hWmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) hS
  have hW : Z ≤ W ∧ P W := by
    simpa [S] using hWmem
  refine ⟨W, hW.1, hW.2, ?_⟩
  intro X hWX hPX
  have hZX : Z ≤ X := le_trans hW.1 hWX
  have hXmem : X ∈ S := by
    simp [S, hZX, hPX]
  have hcard : X.edgeFinset.card ≤ W.edgeFinset.card := hWmax X hXmem
  have hedges : W.edgeFinset = X.edgeFinset :=
    Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hWX) hcard
  exact le_of_eq (SimpleGraph.edgeFinset_inj.mp hedges).symm