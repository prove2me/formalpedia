-- Prove2me | solution 1 for WilliamsonShmoys.finite_edge_augmentation__p2m_460389d4_31bd_4508_b209_05dd70a4382c_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T15:13:58.263418+00:00
-- url     : https://prove2.me/submissions/92ff0561-92b4-45b2-b1c3-f2623c47ffeb

import Mathlib

set_option autoImplicit false

/-- Finite edge augmentation: repeated single-edge additions reach a connected supergraph. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V) (hG : P G)
    (hstep : ∀ (H : SimpleGraph V), G ≤ H → P H → ¬ H.Connected →
      ∃ (u v : V) (huv : u ≠ v),
        ¬ H.Reachable u v ∧
        ∃ K : SimpleGraph V,
          H ≤ K ∧ P K ∧
          ∀ a b, K.Adj a b ↔
            H.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    ∃ C : SimpleGraph V, G ≤ C ∧ C.Connected ∧ P C := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun C : SimpleGraph V => G ≤ C ∧ P C)
  have hS : S.Nonempty := ⟨G, by simp [S, hG]⟩
  obtain ⟨C, hCS, hmax⟩ :=
    Finset.exists_max_image S (fun C : SimpleGraph V => C.edgeSet.ncard) hS
  have hGC : G ≤ C := (Finset.mem_filter.mp hCS).2.1
  have hPC : P C := (Finset.mem_filter.mp hCS).2.2
  refine ⟨C, hGC, ?_, hPC⟩
  by_contra hconn
  obtain ⟨u, v, -, hnreach, K, hCK, hPK, hadj⟩ := hstep C hGC hPC hconn
  have hKmem : K ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hGC.trans hCK, hPK⟩
  have hle : K.edgeSet.ncard ≤ C.edgeSet.ncard := hmax K hKmem
  have hKadj : K.Adj u v :=
    (hadj u v).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hedge_in : s(u, v) ∈ K.edgeSet := (SimpleGraph.mem_edgeSet K).mpr hKadj
  have hedge_notin : s(u, v) ∉ C.edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    intro h
    exact hnreach h.reachable
  have hssub : C.edgeSet ⊂ K.edgeSet := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨SimpleGraph.edgeSet_mono hCK, fun heq => hedge_notin (heq ▸ hedge_in)⟩
  have hlt : C.edgeSet.ncard < K.edgeSet.ncard :=
    Set.ncard_lt_ncard hssub (Set.toFinite K.edgeSet)
  omega
