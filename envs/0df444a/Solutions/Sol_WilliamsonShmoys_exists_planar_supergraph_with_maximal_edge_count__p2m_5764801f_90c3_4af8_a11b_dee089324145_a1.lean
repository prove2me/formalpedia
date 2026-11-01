-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_maximal_edge_count__p2m_5764801f_90c3_4af8_a11b_dee089324145_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:49:16.407398+00:00
-- url     : https://prove2.me/submissions/c0c98e6c-9a27-4866-ab2e-a4b8616e517a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_small_card_completion__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_insertion__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists (fun K : SimpleGraph V => Exists (fun dK : DecidableRel K.Adj =>
      And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (And (LE.le H K)
          (K.edgeFinset.card =
            (if Fintype.card V < 3 then (Fintype.card V).choose 2
             else 3 * Fintype.card V - 6))))) := by
  by_cases hsmall : Fintype.card V < 3
  · rcases WilliamsonShmoys_planar_small_card_completion__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
      (V := V) H dH hH hsmall with ⟨K, dK, hKd⟩
    rcases hKd with ⟨hK, hHK, hcard⟩
    exact ⟨K, dK, hK, hHK, by simpa [hsmall] using hcard⟩
  · have hV : 3 ≤ Fintype.card V := by omega
    let M : Nat := 3 * Fintype.card V - 6
    have hbound := WilliamsonShmoys_planar_edge_count_upper_bound__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
      (V := V) H dH hH hV
    have hHM : H.edgeFinset.card ≤ M := by simpa [M] using hbound
    have finish : ∀ n : Nat, ∀ (G : SimpleGraph V) (dG : DecidableRel G.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn G → H ≤ G →
        G.edgeFinset.card + n = M →
        Exists (fun K : SimpleGraph V => Exists (fun dK : DecidableRel K.Adj =>
          And (WilliamsonShmoys.HasPlanarDrawingOn K)
            (And (H ≤ K) (K.edgeFinset.card = M)))) := by
      intro n
      induction n with
      | zero =>
          intro G dG hG hHG hEq
          exact ⟨G, dG, hG, hHG, by omega⟩
      | succ n ih =>
          intro G dG hG hHG hEq
          have hlt : G.edgeFinset.card < M := by omega
          have hlt' : G.edgeFinset.card < 3 * Fintype.card V - 6 := by
            simpa [M] using hlt
          rcases WilliamsonShmoys_planar_edge_insertion__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
              (V := V) G dG hG hV hlt' with ⟨K, dK, hKd⟩
          rcases hKd with ⟨hK, hGK, hcard⟩
          have hHK : H ≤ K := le_trans hHG hGK
          have hEq' : K.edgeFinset.card + n = M := by omega
          exact ih K dK hK hHK hEq'
    have hEq : H.edgeFinset.card + (M - H.edgeFinset.card) = M := by omega
    rcases finish (M - H.edgeFinset.card) H dH hH le_rfl hEq with ⟨K, dK, hKd⟩
    rcases hKd with ⟨hK, hHK, hKcard⟩
    exact ⟨K, dK, hK, hHK, by simpa [M, hsmall] using hKcard⟩