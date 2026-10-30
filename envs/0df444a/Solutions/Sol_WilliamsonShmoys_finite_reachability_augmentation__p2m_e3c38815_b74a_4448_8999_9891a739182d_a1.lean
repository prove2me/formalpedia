-- Prove2me | solution 1 for WilliamsonShmoys.finite_reachability_augmentation__p2m_e3c38815_b74a_4448_8999_9891a739182d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:45:45.854074+00:00
-- url     : https://prove2.me/submissions/1372f2b0-c2c4-47c7-ae14-538c7c7156f0

import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_reachability_maximal_extension__p2m_4b768b63_f40c_43e8_b5c3_ae742239053f_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V)
    (hP : P G)
    (hStep : ∀ K : SimpleGraph V, P K → ¬ K.Connected →
      ∃ K' : SimpleGraph V, K ≤ K' ∧ P K' ∧ K.edgeSet.ncard ≤ K'.edgeSet.ncard ∧
        (∀ u v, K.Reachable u v → K'.Reachable u v) ∧
        (∃ u v, ¬ K.Reachable u v ∧ K'.Reachable u v)) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ H.Connected ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hGH, hPH, hGE, hMax⟩ :=
    WilliamsonShmoys.finite_reachability_maximal_extension__p2m_4b768b63_f40c_43e8_b5c3_ae742239053f_a1
      P G hP
  by_contra hGoal
  have hNotConnected : ¬ H.Connected := by
    intro hConnected
    exact hGoal ⟨H, hGH, hPH, hConnected, hGE⟩
  obtain ⟨H', hHH', hPH', hEdges', hReach, u, v, hNotReach, hNewReach⟩ :=
    hStep H hPH hNotConnected
  have hGM' : G ≤ H' := le_trans hGH hHH'
  have hGE' : G.edgeSet.ncard ≤ H'.edgeSet.ncard := le_trans hGE hEdges'
  have hMaxReach := hMax H' hGM' hPH' hGE' hReach
  exact hNotReach (hMaxReach u v hNewReach)