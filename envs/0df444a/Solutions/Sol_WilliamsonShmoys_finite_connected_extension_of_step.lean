-- Prove2me | solution 1 for WilliamsonShmoys.finite_connected_extension_of_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:54:40.772153+00:00
-- url     : https://prove2.me/submissions/5f4d17dc-ec41-4599-ba5c-cc9d06f88bba

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (T : SimpleGraph V)
    (hT : P T)
    (hstep : ∀ (G : SimpleGraph V), T ≤ G → P G → ¬ G.Connected →
      ∃ H : SimpleGraph V,
        G ≤ H ∧ P H ∧ ∃ u v, ¬ G.Reachable u v ∧ H.Adj u v) :
    ∃ S : SimpleGraph V, T ≤ S ∧ P S ∧ S.Connected := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter (fun K => T ≤ K ∧ P K)
  have hS : S.Nonempty := ⟨T, by simp [S, hT]⟩
  obtain ⟨G, hG, hmax⟩ := Finset.exists_max_image S (fun K => K.edgeSet.ncard) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hG hmax
  refine ⟨G, hG.1, hG.2, ?_⟩
  by_contra hc
  obtain ⟨H, hGH, hPH, u, v, hr, hadj⟩ := hstep G hG.1 hG.2 hc
  have h1 := hmax H ⟨hG.1.trans hGH, hPH⟩
  have heq : G.edgeSet = H.edgeSet :=
    Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hGH) h1 (Set.toFinite _)
  have : G = H := SimpleGraph.edgeSet_injective heq
  subst this
  exact hr hadj.reachable
