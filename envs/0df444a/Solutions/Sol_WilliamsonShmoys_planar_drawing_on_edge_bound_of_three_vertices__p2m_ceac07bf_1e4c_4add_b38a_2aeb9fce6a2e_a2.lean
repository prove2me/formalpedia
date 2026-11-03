-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_edge_bound_of_three_vertices__p2m_ceac07bf_1e4c_4add_b38a_2aeb9fce6a2e_a2
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:53:08.639887+00:00
-- url     : https://prove2.me/submissions/e582d586-da08-4cde-be57-7e6265f66cdc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
        (hN : HasPlanarDrawingOn N),
        (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
          3 * Fintype.card V ≤ N.edgeFinset.card + 6)) := by
  intro h
  have hV : 3 ≤ Fintype.card (Fin 3) := by simp
  have hN : HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 3)) := by
    unfold HasPlanarDrawingOn
    refine ⟨fun i => ((i.val : ℝ), 0), (fun _ _ _ => (0, 0)), ?_, ?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      have hh : (i.val : ℝ) = (j.val : ℝ) := by
        simpa using congrArg Prod.fst hij
      exact_mod_cast hh
    · intro u v huv hadj
      simp at hadj
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      simp at hadj₁
  have hcard (inst : Fintype (⊥ : SimpleGraph (Fin 3)).edgeSet) :
      (@SimpleGraph.edgeFinset (Fin 3) ⊥ inst).card = 0 := by
    letI := inst
    apply Finset.card_eq_zero.mpr
    apply Finset.ext
    intro e
    simp only [SimpleGraph.mem_edgeFinset, Finset.notMem_empty, iff_false]
    simp
  have hbad := h (V := Fin 3) (⊥ : SimpleGraph (Fin 3)) hV hN
  simp only [hcard, Fintype.card_fin] at hbad
  omega
