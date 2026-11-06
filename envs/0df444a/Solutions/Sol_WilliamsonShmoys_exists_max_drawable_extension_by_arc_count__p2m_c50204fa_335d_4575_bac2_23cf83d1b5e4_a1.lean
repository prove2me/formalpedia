-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_drawable_extension_by_arc_count__p2m_c50204fa_335d_4575_bac2_23cf83d1b5e4_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:30:32.527853+00:00
-- url     : https://prove2.me/submissions/dd2dad9a-3dfc-4f4e-a8b5-fbdb9e3c64b8

-- ID: b2c849ac-8790-42ab-867e-5ff846a44719 | NAME: WilliamsonShmoys.exists_max_drawable_extension_by_arc_count__p2m_c50204fa_335d_4575_bac2_23cf83d1b5e4_a1 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, N ≤ L → HasPlanarDrawingOn L →
          Nat.card {p : V × V // K.Adj p.1 p.2} ≤
            Nat.card {p : V × V // L.Adj p.1 p.2} := by
  classical
  refine ⟨N, le_rfl, hNdraw, ?_⟩
  intro L hNL _hL
  change ({p : V × V | N.Adj p.1 p.2} : Set (V × V)).ncard ≤
      ({p : V × V | L.Adj p.1 p.2} : Set (V × V)).ncard
  apply Set.ncard_le_ncard
  · intro q hq
    exact hNL (show N.Adj q.1 q.2 from hq)
  · exact Set.toFinite _
