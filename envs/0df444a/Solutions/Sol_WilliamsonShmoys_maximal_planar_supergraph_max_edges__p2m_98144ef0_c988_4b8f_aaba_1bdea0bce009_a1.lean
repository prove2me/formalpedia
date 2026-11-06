-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_max_edges__p2m_98144ef0_c988_4b8f_aaba_1bdea0bce009_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:02:20.982139+00:00
-- url     : https://prove2.me/submissions/78e7e512-6d7f-4786-89ea-72720901f51d

-- ID: 7c956806-2ea1-472c-9837-05b1b852605b | NAME: WilliamsonShmoys.maximal_planar_supergraph_max_edges__p2m_98144ef0_c988_4b8f_aaba_1bdea0bce009_a1 | 未本地编译验证
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, K ≤ M → HasPlanarDrawingOn M →
        Nat.card {e : Sym2 V // e ∈ M.edgeSet} ≤
          Nat.card {e : Sym2 V // e ∈ L.edgeSet}) := by
  classical
  let s : Set (SimpleGraph V) := {N | K ≤ N ∧ HasPlanarDrawingOn N}
  have hsne : s.Nonempty := ⟨K, by simp [s, hDraw]⟩
  have hsfinite : s.Finite := s.toFinite
  obtain ⟨L, hLs, hmax⟩ :=
    Set.exists_max_image s
      (fun N : SimpleGraph V => Nat.card {e : Sym2 V // e ∈ N.edgeSet}) hsfinite hsne
  have hLs' : K ≤ L ∧ HasPlanarDrawingOn L := by simpa [s] using hLs
  refine ⟨L, hLs'.1, hLs'.2, ?_⟩
  intro M hKM hM
  exact hmax M (by simpa [s] using (show K ≤ M ∧ HasPlanarDrawingOn M from ⟨hKM, hM⟩))
