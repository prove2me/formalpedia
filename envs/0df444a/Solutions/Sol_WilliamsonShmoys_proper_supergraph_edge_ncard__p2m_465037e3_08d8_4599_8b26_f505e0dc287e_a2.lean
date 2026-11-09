-- Prove2me | solution 1 for WilliamsonShmoys.proper_supergraph_edge_ncard__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:43:12.280951+00:00
-- url     : https://prove2.me/submissions/c039a2e7-e3b9-4108-9904-664989e32154

import Mathlib

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} (H K : SimpleGraph V) (hHK : ∀ u v, H.Adj u v → K.Adj u v) (hne : H ≠ K), H.edgeSet.ncard < K.edgeSet.ncard) := by
  intro claimed
  -- V = ℕ, H = ⊥, K = ⊤: both edge sets have ncard 0 (the second because it is infinite).
  have hne : (⊥ : SimpleGraph ℕ) ≠ ⊤ := by
    intro h
    have h01 : (⊤ : SimpleGraph ℕ).Adj 0 1 := by simp
    rw [← h] at h01
    simp at h01
  have hinf : (⊤ : SimpleGraph ℕ).edgeSet.Infinite := by
    have hinj : Function.Injective (fun n : ℕ => (s(0, n + 1) : Sym2 ℕ)) := by
      intro a b hab
      simp only [Sym2.eq_iff] at hab
      omega
    exact Set.infinite_of_injective_forall_mem hinj (fun n => by simp)
  have h := claimed (⊥ : SimpleGraph ℕ) ⊤ (fun u v huv => by simp at huv) hne
  rw [SimpleGraph.edgeSet_bot, Set.ncard_empty, hinf.ncard] at h
  exact lt_irrefl 0 h

#print axioms solution
