-- Prove2me | solution 1 for WilliamsonShmoys.planar_coherent_root_path_decomposition
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T22:36:44.358992+00:00
-- url     : https://prove2.me/submissions/523067c5-0e16-4a4d-a64d-3557f534b825
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
import Theorems.Thm_WilliamsonShmoys_coherent_paths_spanning_tree
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subset_triangulation
import Theorems.Thm_WilliamsonShmoys_triangular_map_cotree_isTree
import Theorems.Thm_WilliamsonShmoys_triangular_map_descendant_faces_connected
import Theorems.Thm_WilliamsonShmoys_planar_coherent_root_path_decomposition_from_tree_map

set_option autoImplicit false

theorem solution
    {n : Nat} (G : SimpleGraph (Fin n)) (root : Fin n)
    (hG : WilliamsonShmoys.HasPlanarDrawing G)
    (P : (v : {x : Fin n // G.Reachable root x}) -> G.Walk root v.val)
    (hpath : forall v, (P v).IsPath)
    (hprefix : forall u v : {x : Fin n // G.Reachable root x},
      u.val ∈ (P v).support -> (P u).IsSubwalk (P v)) :
    exists (T : Type) (_ : Fintype T) (t : SimpleGraph T)
      (X : T -> Finset {x : Fin n // G.Reachable root x}),
      RobertsonSeymour1986.GM5.IsTreeDecomposition
        (G.induce {x : Fin n | G.Reachable root x}) t X ∧
      forall s, exists a b c : {x : Fin n // G.Reachable root x},
        forall v, v ∈ X s ->
          v.val ∈ (P a).support ∨
          v.val ∈ (P b).support ∨
          v.val ∈ (P c).support := by
  classical
  let S : Type := {x : Fin n // G.Reachable root x}
  let r : S := ⟨root, SimpleGraph.Reachable.refl root⟩
  have small_case (a b c : S) (hc : forall v : S, v = a ∨ v = b ∨ v = c) :
      exists (T : Type) (_ : Fintype T) (t : SimpleGraph T) (X : T -> Finset S),
        RobertsonSeymour1986.GM5.IsTreeDecomposition
          (G.induce {x : Fin n | G.Reachable root x}) t X ∧
        forall s, exists a b c : S, forall v, v ∈ X s ->
          v.val ∈ (P a).support ∨ v.val ∈ (P b).support ∨
            v.val ∈ (P c).support := by
    refine ⟨Unit, inferInstance, ⊥, fun _ => Finset.univ, ?_, ?_⟩
    · refine ⟨SimpleGraph.IsTree.of_subsingleton, ?_, ?_, ?_⟩
      · intro v
        exact ⟨(), Finset.mem_univ v⟩
      · intro x y hxy
        exact ⟨(), Finset.mem_univ x, Finset.mem_univ y⟩
      · intro s s' s'' p hp hs v hv
        exact Finset.mem_univ v
    · intro s
      refine ⟨a, b, c, ?_⟩
      intro v hv
      rcases hc v with h | h | h
      · subst v
        exact Or.inl (P a).end_mem_support
      · subst v
        exact Or.inr (Or.inl (P b).end_mem_support)
      · subst v
        exact Or.inr (Or.inr (P c).end_mem_support)
  by_cases hlarge : exists a b c : S, a ≠ b ∧ a ≠ c ∧ b ≠ c
  · have hcard : 3 <= Fintype.card S := by
      obtain ⟨a, b, c, hab, hac, hbc⟩ := hlarge
      have hh := Finset.card_le_card (Finset.subset_univ ({a, b, c} : Finset S))
      simpa [hab, hac, hbc] using hh
    obtain ⟨R, hRG, hR, Q, hQ, hsupport⟩ :=
      WilliamsonShmoys.coherent_paths_spanning_tree G root P hpath hprefix
    obtain ⟨H, hGH, m, M, heuler⟩ :=
      WilliamsonShmoys.planar_drawing_subset_triangulation G hG
        {x : Fin n | G.Reachable root x} hcard
    have hRH : R <= H := le_trans hRG hGH
    have hD : (M.cotree R).IsTree :=
      WilliamsonShmoys.triangular_map_cotree_isTree M (by simpa using heuler) R hRH hR
    have hFace : forall v : S,
        ((M.cotree R).induce
          {f : Fin m | exists i : Fin 3, v ∈ (Q (M.corner f i)).support}).Connected := by
      intro v
      exact WilliamsonShmoys.triangular_map_descendant_faces_connected
        M R hRH hR r Q hQ v
    obtain ⟨T, hT, t, X, hdecomp, hcoverQ⟩ :=
      WilliamsonShmoys.planar_coherent_root_path_decomposition_from_tree_map
        G root R hRG hR Q hQ H hGH m M hRH hD hFace
    refine ⟨T, hT, t, X, hdecomp, ?_⟩
    intro s
    obtain ⟨a, b, c, hcover⟩ := hcoverQ s
    refine ⟨a, b, c, ?_⟩
    intro v hv
    rcases hcover v hv with ha | hb | hc
    · exact Or.inl ((hsupport v a).mp ha)
    · exact Or.inr (Or.inl ((hsupport v b).mp hb))
    · exact Or.inr (Or.inr ((hsupport v c).mp hc))
  · by_cases hother : exists a : S, a ≠ r
    · obtain ⟨a, har⟩ := hother
      apply small_case r a r
      intro v
      by_cases hvr : v = r
      · exact Or.inl hvr
      · by_cases hva : v = a
        · exact Or.inr (Or.inl hva)
        · exact False.elim (hlarge ⟨r, a, v, Ne.symm har, Ne.symm hvr, Ne.symm hva⟩)
    · apply small_case r r r
      intro v
      left
      by_contra hvr
      exact hother ⟨v, hvr⟩