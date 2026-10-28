-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_of_local_bridge_insertions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:52.643639+00:00
-- url     : https://prove2.me/submissions/311edc6e-2490-47e5-a142-fcfc8d8de44a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hStep : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → ¬ K.Connected →
      ∃ u v : V, ∃ L : SimpleGraph V,
        ¬ K.Reachable u v ∧
        ¬ K.Adj u v ∧
        L.Adj u v ∧
        (∀ x y, K.Adj x y → L.Adj x y) ∧
        (∀ x y, L.Adj x y →
          K.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧
        WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  classical
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K))
    (fun K => K.edgeSet.ncard) ⟨G, by simp [hG]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH hmax
  refine ⟨H, hmax G hG, ?_, hH⟩
  by_contra hc
  obtain ⟨u, v, L, -, hnot, hL, hsub, -, hLd⟩ := hStep H hH hc
  have hss : H.edgeSet ⊂ L.edgeSet := by
    refine ⟨fun e he => ?_, fun h => hnot ?_⟩
    · induction e using Sym2.ind with
      | h x y => exact hsub x y he
    · exact h (show s(u, v) ∈ L.edgeSet from hL)
  have := Set.ncard_lt_ncard hss (Set.toFinite _)
  have := hmax L hLd
  omega
