-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_induce__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:33:16.535211+00:00
-- url     : https://prove2.me/submissions/3f55463d-dcc8-4796-a022-3c735d216451

-- ID: 8371b57d-0d75-43a4-a61c-a7d39fc2e689 | NAME: WilliamsonShmoys.planar_drawing_induce__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a1 | 未本地编译验证
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (S : Finset V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    WilliamsonShmoys.HasPlanarDrawingOn (K.induce (↑S : Set V)) := by
  classical
  rcases hK with ⟨p, arc, hp, hsingle, hpair⟩
  refine ⟨(fun u : (S : Set V) => p u.1),
    (fun (u v : (S : Set V)) t => arc u.1 v.1 t), ?_, ?_, ?_⟩
  · intro u v hEq
    exact Subtype.ext (hp hEq)
  · intro u v huv huv_adj
    have huv' : u.1 < v.1 := by simpa using huv
    have hadj : K.Adj u.1 v.1 := by simpa using huv_adj
    rcases hsingle u.1 v.1 huv' hadj with ⟨hc, hi, h0, h1, hav⟩
    refine ⟨hc, hi, h0, h1, ?_⟩
    intro t ht w
    exact hav t ht w.1
  · intro u v x y huv hxy huv_adj hxy_adj hne t ht s' hs' heq
    have huv' : u.1 < v.1 := by simpa using huv
    have hxy' : x.1 < y.1 := by simpa using hxy
    have hadj : K.Adj u.1 v.1 := by simpa using huv_adj
    have hadj' : K.Adj x.1 y.1 := by simpa using hxy_adj
    have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro h
      apply hne
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))
    exact hpair u.1 v.1 x.1 y.1 huv' hxy' hadj hadj' hne' t ht s' hs' heq
