-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_planar_extension__p2m_10fbf93e_9f1f_430c_8d69_9a023f7a87fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:32:52.3732+00:00
-- url     : https://prove2.me/submissions/954fd443-d729-4590-9486-22c19270e862

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeFinset ⊆ N.edgeFinset ∧
      ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn K →
        N.edgeFinset ⊆ K.edgeFinset →
        K.edgeFinset ⊆ N.edgeFinset := by
  classical
  let p : SimpleGraph V → Prop := fun K =>
    WilliamsonShmoys.HasPlanarDrawingOn K ∧ M ≤ K
  obtain ⟨N, dN, hN⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (V := V) p).2
      ⟨M, ⟨hM, le_rfl⟩⟩
  have hpN : p N := hN.prop
  change WilliamsonShmoys.HasPlanarDrawingOn N ∧ M ≤ N at hpN
  rcases hpN with ⟨hPlanN, hMN⟩
  refine ⟨N, dN, hPlanN, SimpleGraph.edgeFinset_subset_edgeFinset.mpr hMN, ?_⟩
  intro K dK hPlanK hNK
  letI : DecidableRel K.Adj := dK
  have hMK : M ≤ K :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mp
      ((SimpleGraph.edgeFinset_subset_edgeFinset.mpr hMN).trans hNK)
  have hpK : p K := ⟨hPlanK, hMK⟩
  have hmax : K.edgeFinset.card ≤ N.edgeFinset.card := hN.2 hpK
  have heq : N.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hNK hmax
  intro e he
  rw [heq]
  exact he