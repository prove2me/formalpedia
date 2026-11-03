-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_d0cbf8fc_b126_4e9b_9c59_f16faa272cb9_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:09:58.202202+00:00
-- url     : https://prove2.me/submissions/abc710e2-e6f1-4486-8367-8ba3b74c2669

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
        (hcard : 3 ≤ Fintype.card V)
        (hmax : ∀ H' : SimpleGraph V,
          (∀ {u v : V}, H'.Adj u v → H.Adj u v) →
          HasPlanarDrawingOn H' → H' = H),
        letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
          fun G => Classical.decRel G.Adj
        3 * Fintype.card V - 6 ≤ H.edgeFinset.card) := by
  intro hall
  let V := Fin 3
  let H : SimpleGraph V := ⊥
  have hH : HasPlanarDrawingOn H := by
    refine ⟨(fun i => ((i.val : ℝ), 0)), (fun _ _ _ => (0, 0)), ?_, ?_, ?_⟩
    · intro i j hij
      have hval : (i.val : ℝ) = (j.val : ℝ) := by
        simpa using congrArg Prod.fst hij
      exact Fin.ext (Nat.cast_injective hval)
    · intro u v huv hadj
      simp [H] at hadj
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      simp [H] at hadj
  have hcard : 3 ≤ Fintype.card V := by
    simp [V]
  have hmax : ∀ H' : SimpleGraph V,
      (∀ {u v : V}, H'.Adj u v → H.Adj u v) →
      HasPlanarDrawingOn H' → H' = H := by
    intro H' hsub hplanar
    ext u v
    constructor
    · intro huv
      have hsub_huv := hsub huv
      simpa [H] using hsub_huv
    · intro huv
      simp [H] at huv
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  have hbad := @hall V inferInstance inferInstance H hH hcard hmax
  have hzero : (@SimpleGraph.edgeFinset V H H.fintypeEdgeSet).card = 0 := by
    simp [SimpleGraph.edgeFinset, H]
  rw [hzero] at hbad
  norm_num [V] at hbad
