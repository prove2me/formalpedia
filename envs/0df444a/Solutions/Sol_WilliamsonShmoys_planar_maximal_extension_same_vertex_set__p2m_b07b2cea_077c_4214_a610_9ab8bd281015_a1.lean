-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension_same_vertex_set__p2m_b07b2cea_077c_4214_a610_9ab8bd281015_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:17.122731+00:00
-- url     : https://prove2.me/submissions/431c2fb3-9033-43f8-bd4f-4c6f4a83f991
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_mem_of_finite__p2m_4f4a8988_3a83_4c97_870a_3e268ffa4b52_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    exists L : SimpleGraph V,
      K <= L /\ WilliamsonShmoys.HasPlanarDrawingOn L /\
      (forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) := by
  classical
  let P : SimpleGraph V -> Prop :=
    fun L => K <= L /\ WilliamsonShmoys.HasPlanarDrawingOn L
  have hne : exists L : SimpleGraph V, P L :=
    Exists.intro K (And.intro le_rfl hK)
  obtain ⟨L, hPL, hmax⟩ :=
    exists_maximal_mem_of_finite__p2m_4f4a8988_3a83_4c97_870a_3e268ffa4b52_a1 P hne
  refine Exists.intro L (And.intro hPL.1 (And.intro hPL.2 ?_))
  intro M hLM hM
  apply hmax M hLM
  exact And.intro (le_trans hPL.1 hLM) hM