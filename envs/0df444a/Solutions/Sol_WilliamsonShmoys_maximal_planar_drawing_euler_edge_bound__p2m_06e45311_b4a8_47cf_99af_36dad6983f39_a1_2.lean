-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_euler_edge_bound__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:50:32.884436+00:00
-- url     : https://prove2.me/submissions/ff08a2dd-b65e-4bde-9ea2-54f98b5363fa

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
        H.edgeFinset.card = 3 * Fintype.card V - 6) := by
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
