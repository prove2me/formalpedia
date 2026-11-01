-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_induce__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:15:10.240604+00:00
-- url     : https://prove2.me/submissions/c39a4efe-d9f8-4e8b-af5d-fd8802f97e73

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (S : Finset V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    WilliamsonShmoys.HasPlanarDrawingOn (K.induce (↑S : Set V)) := by
  rcases hK with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨(fun u : ↑S => p u.1), (fun u v t => arc u.1 v.1 t), ?_, ?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    apply hp
    exact huv
  · intro u v huv hadj
    have huv' : u.1 < v.1 := huv
    have hadj' : K.Adj u.1 v.1 := hadj
    rcases hedge u.1 v.1 huv' hadj' with ⟨hcont, hinj, hzero, hone, havoids⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa using hcont
    · simpa using hinj
    · simpa using hzero
    · simpa using hone
    · intro t ht w
      exact havoids t ht w.1
  · intro u v x y huv hxy hadjuv hadjxy hne t ht s hs heq
    have huv' : u.1 < v.1 := huv
    have hxy' : x.1 < y.1 := hxy
    have hadjuv' : K.Adj u.1 v.1 := hadjuv
    have hadjxy' : K.Adj x.1 y.1 := hadjxy
    have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro hvals
      apply hne
      have hu : u = x := Subtype.ext (congrArg Prod.fst hvals)
      have hv : v = y := Subtype.ext (congrArg Prod.snd hvals)
      exact Prod.ext hu hv
    have hcross' := hcross u.1 v.1 x.1 y.1 huv' hxy' hadjuv' hadjxy' hne' t ht s hs
    simpa using hcross' heq