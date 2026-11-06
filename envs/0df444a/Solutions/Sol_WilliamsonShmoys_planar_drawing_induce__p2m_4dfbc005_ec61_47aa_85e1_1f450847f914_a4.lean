-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_induce__p2m_4dfbc005_ec61_47aa_85e1_1f450847f914_a4
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:58:15.082204+00:00
-- url     : https://prove2.me/submissions/68a0d2dd-ee73-4c72-8111-2b7697d5ef06

-- ID: 98bb09a3-5fff-4d40-87aa-050eb50db2d4 | NAME: WilliamsonShmoys.planar_drawing_induce__p2m_4dfbc005_ec61_47aa_85e1_1f450847f914_a4 | 未本地编译验证
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (s : Set V)
    [Fintype {x // x ∈ s}]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    WilliamsonShmoys.HasPlanarDrawingOn (M.induce s) := by
  rcases hM with ⟨p, arc, hp, hsingle, hpair⟩
  refine ⟨(fun u : s => p u.1),
    (fun (u v : s) t => arc u.1 v.1 t), ?_, ?_, ?_⟩
  · intro u v hEq
    exact Subtype.ext (hp hEq)
  · intro u v huv huv_adj
    have huv' : u.1 < v.1 := by simpa using huv
    have hadj : M.Adj u.1 v.1 := by simpa using huv_adj
    rcases hsingle u.1 v.1 huv' hadj with ⟨hc, hi, h0, h1, hav⟩
    refine ⟨hc, hi, h0, h1, ?_⟩
    intro t ht w
    exact hav t ht w.1
  · intro u v x y huv hxy huv_adj hxy_adj hne t ht s' hs' heq
    have huv' : u.1 < v.1 := by simpa using huv
    have hxy' : x.1 < y.1 := by simpa using hxy
    have hadj : M.Adj u.1 v.1 := by simpa using huv_adj
    have hadj' : M.Adj x.1 y.1 := by simpa using hxy_adj
    have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro h
      apply hne
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))
    exact hpair u.1 v.1 x.1 y.1 huv' hxy' hadj hadj' hne' t ht s' hs' heq
