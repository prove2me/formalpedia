-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_induce__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:37:34.675172+00:00
-- url     : https://prove2.me/submissions/a1be685c-8575-4583-9aa3-a218294fae95

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (s : Set V) :
    letI : Fintype {v // v ∈ s} := Fintype.ofFinite _
    HasPlanarDrawingOn (N.induce s) := by
  classical
  rcases hN with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨fun v => p v.1, fun u v t => arc u.1 v.1 t, ?_, ?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    exact hp hab
  · intro u v huv hadj
    change N.Adj u.1 v.1 at hadj
    rcases hedge u.1 v.1 huv hadj with ⟨hcont, hinj, hzero, hone, havoid⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change ContinuousOn (arc u.1 v.1) (Set.Icc 0 1)
      exact hcont
    · change Set.InjOn (arc u.1 v.1) (Set.Icc 0 1)
      exact hinj
    · change arc u.1 v.1 0 = p u.1
      exact hzero
    · change arc u.1 v.1 1 = p v.1
      exact hone
    · intro t ht w
      change arc u.1 v.1 t ≠ p w.1
      exact havoid t ht w.1
  · intro u v x y huv hxy hadjuv hadjxy hne t ht s' hs' heq
    change N.Adj u.1 v.1 at hadjuv
    change N.Adj x.1 y.1 at hadjxy
    have hpair : (u.1, v.1) ≠ (x.1, y.1) := by
      intro heq'
      apply hne
      have hu : u = x := Subtype.ext (congrArg Prod.fst heq')
      have hv : v = y := Subtype.ext (congrArg Prod.snd heq')
      exact Prod.ext hu hv
    exact hcross u.1 v.1 x.1 y.1 huv hxy hadjuv hadjxy hpair t ht s' hs' heq