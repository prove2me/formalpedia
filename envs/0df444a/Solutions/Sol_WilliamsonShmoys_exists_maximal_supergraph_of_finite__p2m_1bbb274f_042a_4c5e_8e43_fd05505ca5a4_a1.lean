-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_1bbb274f_042a_4c5e_8e43_fd05505ca5a4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:28:06.653124+00:00
-- url     : https://prove2.me/submissions/ba7e0254-05f5-4793-a0ae-a0fa688b72ea

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_finset_maximal__p2m_d87be54e_bfcb_4aba_9277_804ad42ab6ab_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    ∃ K : SimpleGraph V, P K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      (∀ L : SimpleGraph V, P L →
        (∀ u v, K.Adj u v → L.Adj u v) →
        (∀ u v, L.Adj u v → K.Adj u v)) := by
  classical
  let s : Finset (SimpleGraph V) := Finset.univ.filter fun K => P K ∧ H ≤ K
  have hs : s.Nonempty := by
    refine ⟨H, ?_⟩
    simp [s, hP]
  obtain ⟨K, hKs, hmax⟩ :=
    finite_finset_maximal__p2m_d87be54e_bfcb_4aba_9277_804ad42ab6ab_a1 s hs
  have hK : P K ∧ H ≤ K := by
    simpa [s] using hKs
  refine ⟨K, hK.1, ?_, ?_⟩
  · intro u v huv
    exact hK.2 huv
  · intro L hPL hKL
    have hHL : H ≤ L := le_trans hK.2 hKL
    exact hmax L (by simp [s, hPL, hHL]) hKL