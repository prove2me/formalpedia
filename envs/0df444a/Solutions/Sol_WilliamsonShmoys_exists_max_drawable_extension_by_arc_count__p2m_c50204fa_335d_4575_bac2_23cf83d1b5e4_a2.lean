-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_drawable_extension_by_arc_count__p2m_c50204fa_335d_4575_bac2_23cf83d1b5e4_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:31:07.290228+00:00
-- url     : https://prove2.me/submissions/26b498b0-e4b2-4da5-b85b-9e77bb69de9b

-- ID: a293a04d-6e80-4514-9ece-79baf83104e1 | NAME: WilliamsonShmoys.exists_max_drawable_extension_by_arc_count__p2m_c50204fa_335d_4575_bac2_23cf83d1b5e4_a2 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      N ≤ K ∧ HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, N ≤ L → HasPlanarDrawingOn L →
          Nat.card {p : V × V // K.Adj p.1 p.2} ≥
            Nat.card {p : V × V // L.Adj p.1 p.2} := by
  classical
  let s : Set (SimpleGraph V) := {K | N ≤ K ∧ HasPlanarDrawingOn K}
  have hsne : s.Nonempty := ⟨N, by simp [s, hNdraw]⟩
  have hsfinite : s.Finite := s.toFinite
  obtain ⟨K, hKs, hmax⟩ :=
    Set.exists_max_image s
      (fun G : SimpleGraph V => Nat.card {p : V × V // G.Adj p.1 p.2})
      hsfinite hsne
  have hKs' : N ≤ K ∧ HasPlanarDrawingOn K := by simpa [s] using hKs
  refine ⟨K, hKs'.1, hKs'.2, ?_⟩
  intro L hNL hL
  exact hmax L (by simp [s, hNL, hL])
