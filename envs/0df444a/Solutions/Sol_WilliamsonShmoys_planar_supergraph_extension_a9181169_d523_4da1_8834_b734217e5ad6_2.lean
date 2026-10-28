-- Prove2me | solution 2 for WilliamsonShmoys.planar_supergraph_extension_a9181169_d523_4da1_8834_b734217e5ad6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T03:38:21.701083+00:00
-- url     : https://prove2.me/submissions/10df2a39-5f03-4e89-bd83-0a65e19f1841

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem S195_gen
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (N : SimpleGraph V) (hP : P N) :
    ∃ H : SimpleGraph V, N ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter (fun K => N ≤ K ∧ P K)
  have hS : S.Nonempty := ⟨N, by simp [S, hP]⟩
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image S (fun K => K.edgeSet.ncard) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hH hmax
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hHK hK
  have h1 := hmax K ⟨hH.1.trans hHK, hK⟩
  have heq : H.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hHK) h1 (Set.toFinite _)
  exact (SimpleGraph.edgeSet_injective heq).symm


open WilliamsonShmoys in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V, HasPlanarDrawingOn T ∧
      (∀ u v, G.Adj u v → T.Adj u v) ∧
      (∀ U : SimpleGraph V, HasPlanarDrawingOn U →
        (∀ u v, T.Adj u v → U.Adj u v) → U = T) := by
  obtain ⟨H, h1, h2, h3⟩ := S195_gen (fun K => HasPlanarDrawingOn K) G hG
  exact ⟨H, h2, fun u v h => h1 h, fun U hU hTU => h3 U (fun u v h => hTU u v h) hU⟩
