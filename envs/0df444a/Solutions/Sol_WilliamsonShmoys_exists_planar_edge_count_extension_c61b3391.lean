-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_edge_count_extension_c61b3391
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:01:41.944223+00:00
-- url     : https://prove2.me/submissions/942d00cc-8c3d-488a-a16d-706609bdc559

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_c61b3391
import Theorems.Thm_WilliamsonShmoys_planar_single_edge_augmentation_c61b3391

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ T : SimpleGraph V,
      K ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  let b : Nat := 3 * Fintype.card V - 6
  have hbound : K.edgeSet.ncard ≤ b :=
    WilliamsonShmoys.planar_edge_count_upper_bound_c61b3391 K hV hK
  have hiterate :
      ∀ d : Nat, ∀ G : SimpleGraph V,
        K ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G →
        G.edgeSet.ncard + d = b →
        ∃ T : SimpleGraph V,
          K ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
            T.edgeSet.ncard = b := by
    intro d
    induction d with
    | zero =>
        intro G hKG hG hc
        refine ⟨G, hKG, hG, ?_⟩
        omega
    | succ d ih =>
        intro G hKG hG hc
        have hlt : G.edgeSet.ncard < b := by omega
        obtain ⟨H, hGH, hH, hcount⟩ :=
          WilliamsonShmoys.planar_single_edge_augmentation_c61b3391 G hV hG hlt
        have hc' : H.edgeSet.ncard + d = b := by omega
        exact ih H (le_trans hKG hGH) hH hc'
  have hstart : K.edgeSet.ncard + (b - K.edgeSet.ncard) = b := by
    omega
  exact hiterate (b - K.edgeSet.ncard) K le_rfl hK hstart