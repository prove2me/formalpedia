-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_component__p2m_3a2545dd_3002_4f8f_92b3_b56d526d92af_a3
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:42:48.549283+00:00
-- url     : https://prove2.me/submissions/aa3c863e-ee9f-49ed-ba49-34e467a4e090

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (c : G.ConnectedComponent)
    [Fintype c.supp] :
    HasPlanarDrawingOn (G.induce c.supp) ∧ (G.induce c.supp).Connected := by
  classical
  constructor
  · rcases hG with ⟨p, arc, hp, hedge, hcross⟩
    refine ⟨(fun x : c.supp => p x.1),
      (fun (x y : c.supp) (t : ℝ) => arc x.1 y.1 t), ?_, ?_, ?_⟩
    · intro x y hxy
      exact Subtype.ext (hp hxy)
    · intro u v huv hadj
      have huv' : (u : V) < (v : V) := by simpa using huv
      have hadjV : G.Adj u.1 v.1 := by
        simpa only [SimpleGraph.induce_adj] using hadj
      rcases hedge u.1 v.1 huv' hadjV with ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, h2, h3, h4, ?_⟩
      intro t ht w
      exact h5 t ht w.1
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      have huv' : (u : V) < (v : V) := by simpa using huv
      have hxy' : (x : V) < (y : V) := by simpa using hxy
      have hadjV : G.Adj u.1 v.1 := by
        simpa only [SimpleGraph.induce_adj] using hadj
      have hadjV' : G.Adj x.1 y.1 := by
        simpa only [SimpleGraph.induce_adj] using hadj'
      have hneV : (u.1, v.1) ≠ (x.1, y.1) := by
        intro h
        apply hne
        exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
          (Subtype.ext (congrArg Prod.snd h))
      exact hcross u.1 v.1 x.1 y.1 huv' hxy' hadjV hadjV' hneV t ht s hs heq
  · simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using
      (SimpleGraph.ConnectedComponent.connected_toSimpleGraph c)
