-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_equation_from_planar_drawing__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:29:56.953268+00:00
-- url     : https://prove2.me/submissions/98538572-6789-447c-8a09-5d515ec58fb6

-- ID: 854ca7f2-4a2f-40b5-a832-4330138988cf | NAME: WilliamsonShmoys.planar_drawing_euler_equation_from_planar_drawing__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2 | 未本地编译验证
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ faceCount : ℕ,
      Fintype.card V + faceCount = G.edgeSet.ncard + 2 := by
  classical
  have hle : Fintype.card V ≤ G.edgeFinset.card + 1 := by
    simpa [SimpleGraph.edgeFinset] using hconn.card_vert_le_card_edgeSet_add_one
  have hcard_eq : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset]
    exact (Set.ncard_eq_toFinset_card' G.edgeSet).symm
  rw [hcard_eq] at hle
  refine ⟨G.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega
