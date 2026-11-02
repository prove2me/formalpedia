-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_extension__p2m_ea8ef902_b5b0_4092_a824_9484bf1d76fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:27:28.683759+00:00
-- url     : https://prove2.me/submissions/0c3f639b-556e-496d-bb76-9e486ede144e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : LE.le 3 (Fintype.card V))
    (hNdraw : HasPlanarDrawingOn N) :
    Exists (fun K : SimpleGraph V =>
      And (LE.le N K)
        (And (HasPlanarDrawingOn K)
          (forall L : SimpleGraph V, LE.le K L -> HasPlanarDrawingOn L -> L = K))) := by
  classical
  let p : SimpleGraph V -> Prop := fun G => N <= G /\ HasPlanarDrawingOn G
  have hp : Exists fun G : SimpleGraph V => p G :=
    Exists.intro N (And.intro le_rfl hNdraw)
  obtain ⟨K, hKdec, hK⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (V := V) p).2 hp
  letI : DecidableRel K.Adj := hKdec
  refine Exists.intro K (And.intro hK.1.1 (And.intro hK.1.2 ?_))
  intro L hKL hLdraw
  have hLp : p L := And.intro (le_trans hK.1.1 hKL) hLdraw
  exact ((SimpleGraph.IsExtremal.le_iff_eq hK hLp).mp hKL).symm
