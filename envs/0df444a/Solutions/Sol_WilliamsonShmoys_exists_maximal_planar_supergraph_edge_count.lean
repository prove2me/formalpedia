-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:49:09.905845+00:00
-- url     : https://prove2.me/submissions/25cca65f-181c-4cbd-9d8b-e5b0b147a97d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_fixed_vertex_type_b54e7d04
import Theorems.Thm_WilliamsonShmoys_planar_single_edge_augmentation_below_euler_bound_b54e7d04

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  classical
  let T : ℕ := 3 * Fintype.card V - 6
  have hbound : K.edgeSet.ncard ≤ T := by
    simpa [T] using
      WilliamsonShmoys.planar_edge_bound_for_fixed_vertex_type_b54e7d04 K hV hK
  have hcomplete :
      ∀ d : ℕ, ∀ G : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn G →
        G.edgeSet.ncard ≤ T →
        T - G.edgeSet.ncard = d →
        ∃ L : SimpleGraph V,
          G.edgeSet ⊆ L.edgeSet ∧
          WilliamsonShmoys.HasPlanarDrawingOn L ∧
          L.edgeSet.ncard = T := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro G hG hGbound hdef
        by_cases hd : d = 0
        · subst d
          have hEq : G.edgeSet.ncard = T := by omega
          exact ⟨G, Set.Subset.rfl, hG, hEq⟩
        · have hsmall : G.edgeSet.ncard < T := by omega
          obtain ⟨H, hsub, hH, hcard⟩ :=
            WilliamsonShmoys.planar_single_edge_augmentation_below_euler_bound_b54e7d04
              G hV hG hsmall
          have hHbound : H.edgeSet.ncard ≤ T := by
            simpa [T] using
              WilliamsonShmoys.planar_edge_bound_for_fixed_vertex_type_b54e7d04 H hV hH
          let d' : ℕ := T - H.edgeSet.ncard
          have hdef' : T - H.edgeSet.ncard = d' := rfl
          have hlt : d' < d := by
            dsimp [d']
            rw [hcard]
            omega
          obtain ⟨L, hHL, hL, hLcard⟩ :=
            ih d' hlt H hH hHbound hdef'
          exact ⟨L, Set.Subset.trans hsub.1 hHL, hL, by simpa [T] using hLcard⟩
  simpa [T] using hcomplete (T - K.edgeSet.ncard) K hK hbound rfl