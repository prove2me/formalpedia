-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:49:37.33837+00:00
-- url     : https://prove2.me/submissions/dc8d263e-887b-4916-a7f3-3fe7900e035c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K →
        HasPlanarDrawingOn K → K = H := by
  classical
  let f : SimpleGraph V → V → V → Bool :=
    fun X u v => decide (X.Adj u v)
  have hf : Function.Injective f := by
    intro X Y h
    apply SimpleGraph.ext
    funext u v
    apply propext
    have hxy : decide (X.Adj u v) = decide (Y.Adj u v) := by
      simpa [f] using congrFun (congrFun h u) v
    simpa using Bool.eq_iff_iff.mp hxy
  haveI : Finite (SimpleGraph V) := Finite.of_injective f hf
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let E (X : SimpleGraph V) : Finset (V × V) :=
    Finset.univ.filter fun p => p.1 < p.2 ∧ X.Adj p.1 p.2
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun X => G ≤ X ∧ HasPlanarDrawingOn X
  have hS : S.Nonempty := by
    refine ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hG⟩⟩
  obtain ⟨H, hHmem, hHmax⟩ :=
    Finset.exists_max_image S (fun X => (E X).card) hS
  have hHcond : G ≤ H ∧ HasPlanarDrawingOn H :=
    (Finset.mem_filter.mp hHmem).2
  refine ⟨H, hHcond.1, hHcond.2, ?_⟩
  intro K hHK hK
  have hGK : G ≤ K := le_trans hHcond.1 hHK
  have hKmem : K ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGK, hK⟩
  have hsub : E H ⊆ E K := by
    intro p hp
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, hHK hp.2⟩
  have hcard : (E K).card ≤ (E H).card := hHmax K hKmem
  have hEq : E H = E K := Finset.eq_of_subset_of_card_le hsub hcard
  ext u v
  by_cases huv : u = v
  · subst v
    simp
  · rcases lt_or_gt_of_ne huv with huv | hvu
    · have hHu : H.Adj u v ↔ (u, v) ∈ E H := by
        simp [E, huv]
      have hKv : K.Adj u v ↔ (u, v) ∈ E K := by
        simp [E, huv]
      rw [hHu, hKv, hEq]
    · have hHu : H.Adj u v ↔ (v, u) ∈ E H := by
        rw [SimpleGraph.adj_comm]
        simp [E, hvu]
      have hKv : K.Adj u v ↔ (v, u) ∈ E K := by
        rw [SimpleGraph.adj_comm]
        simp [E, hvu]
      rw [hHu, hKv, hEq]