-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph__p2m_13d6333d_8327_4de0_a7db_2786f76107ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:32.61199+00:00
-- url     : https://prove2.me/submissions/fad354c1-9961-48d1-a184-7f05e9c99917

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (P : SimpleGraph V -> Prop) (hP : P Q) :
    Exists fun R : SimpleGraph V =>
      And (Set.Subset Q.edgeSet R.edgeSet)
        (And (P R)
          (forall S : SimpleGraph V,
            Set.Subset R.edgeSet S.edgeSet ->
            P S ->
            Set.Subset S.edgeSet R.edgeSet)) := by
  classical
  obtain ⟨R, hQR, hRmax⟩ := Finite.exists_le_maximal hP
  refine ⟨R, SimpleGraph.edgeSet_subset_edgeSet.mpr hQR, hRmax.1, ?_⟩
  intro S hRS hS
  have hRS' : R ≤ S := SimpleGraph.edgeSet_subset_edgeSet.mp hRS
  have hEq : R = S := hRmax.eq_of_le hS hRS'
  intro e he
  simpa [hEq] using he