-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_edge_bound__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:32:22.690613+00:00
-- url     : https://prove2.me/submissions/d7a86b3d-5bde-4f67-9a6d-367d5d6efff8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_278b0a4b_e4b3_4f5b_934c_d513e35b19a5_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (c : K.ConnectedComponent) :
    letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
    letI : DecidableRel ((K.induce c.supp).Adj) := Classical.decRel _
    (K.induce c.supp).edgeFinset.card ≤
      3 * Fintype.card {v : V // v ∈ c.supp} - 3 := by
  letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
  letI : DecidableRel ((K.induce c.supp).Adj) := Classical.decRel _
  have hdraw : HasPlanarDrawingOn (K.induce c.supp) := by
    rcases hK with ⟨p, arc, hp, hedge, hcross⟩
    refine ⟨(fun v : {v : V // v ∈ c.supp} => p v.1),
      (fun u v t => arc u.1 v.1 t), ?_, ?_, ?_⟩
    · intro a b hab
      exact Subtype.ext (hp hab)
    · intro u v huv hadj
      rcases hedge u.1 v.1 huv hadj with ⟨hcont, hinj, h0, h1, hinterior⟩
      exact ⟨hcont, hinj, h0, h1, fun t ht w => hinterior t ht w.1⟩
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      exact hcross u.1 v.1 x.1 y.1 huv hxy hadj₁ hadj₂ (by
        intro heq'
        apply hne
        exact Prod.ext (Subtype.ext (congrArg Prod.fst heq'))
          (Subtype.ext (congrArg Prod.snd heq'))) t ht s hs heq
  exact WilliamsonShmoys.planar_edge_bound__p2m_278b0a4b_e4b3_4f5b_934c_d513e35b19a5_a1
    (K.induce c.supp) hdraw
