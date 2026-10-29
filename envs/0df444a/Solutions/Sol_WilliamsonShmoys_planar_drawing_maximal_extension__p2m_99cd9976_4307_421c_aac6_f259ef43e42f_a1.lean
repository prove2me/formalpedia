-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_99cd9976_4307_421c_aac6_f259ef43e42f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:17:20.593404+00:00
-- url     : https://prove2.me/submissions/49d6a963-2e45-4e64-9e6e-acd888098bc4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    exists M : SimpleGraph V,
      N <= M /\ WilliamsonShmoys.HasPlanarDrawingOn M /\
        forall K : SimpleGraph V, M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = M := by
  classical
  let P : SimpleGraph V -> Prop :=
    fun G => N <= G /\ WilliamsonShmoys.HasPlanarDrawingOn G
  have hNmem : P N := And.intro le_rfl hN
  have hfinite : ({G : SimpleGraph V | P G} : Set (SimpleGraph V)).Finite :=
    Set.toFinite _
  let M : SimpleGraph V := Classical.choose (hfinite.exists_le_maximal hNmem)
  have hM := Classical.choose_spec (hfinite.exists_le_maximal hNmem)
  have hMP : P M := hM.2.1
  refine Exists.intro M (And.intro hM.1 (And.intro hMP.2 ?_))
  intro K hMK hK
  have hKP : P K := And.intro (hM.1.trans hMK) hK
  have hKM : K <= M := hM.2.2 hKP hMK
  exact le_antisymm hKM hMK