-- Prove2me | solution 1 for WilliamsonShmoys.component_planar_drawing__p2m_16ddb684_8eab_45f4_881b_4391d956c1ce_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:46:55.074989+00:00
-- url     : https://prove2.me/submissions/2756abd0-4fdc-46ef-a76e-68b819dedbde

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (C : L.ConnectedComponent)
    [Fintype C.supp] :
    WilliamsonShmoys.HasPlanarDrawingOn C.toSimpleGraph := by
  rcases hL with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨(fun c : C.supp => p c.1), (fun c d t => arc c.1 d.1 t), ?_, ?_, ?_⟩
  · intro c d hcd
    apply Subtype.ext
    exact hp hcd
  · intro c d hlt hadj
    have hlt' : c.1 < d.1 := hlt
    have hadj' : L.Adj c.1 d.1 := hadj
    rcases hedge c.1 d.1 hlt' hadj' with ⟨hcont, hinj, hzero, hone, havoid⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hcont
    · exact hinj
    · exact hzero
    · exact hone
    · intro t ht w
      exact havoid t ht w.1
  · intro c d e f hcd hef hadj1 hadj2 hne t ht s hs heq
    have hcd' : c.1 < d.1 := hcd
    have hef' : e.1 < f.1 := hef
    have hadj1' : L.Adj c.1 d.1 := hadj1
    have hadj2' : L.Adj e.1 f.1 := hadj2
    have hne' : (c.1, d.1) ≠ (e.1, f.1) := by
      intro h
      apply hne
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst h
      · apply Subtype.ext
        exact congrArg Prod.snd h
    exact hcross c.1 d.1 e.1 f.1 hcd' hef' hadj1' hadj2' hne' t ht s hs heq
