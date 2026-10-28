-- Prove2me | solution 1 for WilliamsonShmoys.planar_coherent_root_path_decomposition_from_tree_map
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:30:52.469719+00:00
-- url     : https://prove2.me/submissions/d68310eb-b2a6-4a9c-9140-8b2914b368dc

import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

theorem solution
    {n : Nat} (G : SimpleGraph (Fin n)) (root : Fin n)
    [Fintype {x : Fin n // G.Reachable root x}]
    (R : SimpleGraph {x : Fin n // G.Reachable root x})
    (hRG : R ≤ G.induce {x : Fin n | G.Reachable root x})
    (hR : R.IsTree)
    (Q : (v : {x : Fin n // G.Reachable root x}) →
      R.Walk ⟨root, SimpleGraph.Reachable.refl root⟩ v)
    (hQ : ∀ v, (Q v).IsPath)
    (H : SimpleGraph {x : Fin n // G.Reachable root x})
    (hGH : G.induce {x : Fin n | G.Reachable root x} ≤ H)
    (m : Nat) (M : WilliamsonShmoys.TriangularMap H (Fin m))
    (hRH : R ≤ H)
    (hD : (M.cotree R).IsTree)
    (hFace : ∀ v : {x : Fin n // G.Reachable root x},
      ((M.cotree R).induce
        {f : Fin m | ∃ i : Fin 3, v ∈ (Q (M.corner f i)).support}).Connected) :
    ∃ (T : Type) (_ : Fintype T) (t : SimpleGraph T)
      (X : T → Finset {x : Fin n // G.Reachable root x}),
      RobertsonSeymour1986.GM5.IsTreeDecomposition
        (G.induce {x : Fin n | G.Reachable root x}) t X ∧
      ∀ s, ∃ a b c : {x : Fin n // G.Reachable root x},
        ∀ v ∈ X s,
          v ∈ (Q a).support ∨ v ∈ (Q b).support ∨ v ∈ (Q c).support := by
  classical
  refine ⟨Fin m, inferInstance, M.cotree R,
    fun f => Finset.univ.filter (fun v => ∃ i : Fin 3, v ∈ (Q (M.corner f i)).support),
    ⟨hD, ?_, ?_, ?_⟩, ?_⟩
  · intro v
    obtain ⟨f, i, hfi⟩ := M.vertex_covered v
    refine ⟨f, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, by rw [hfi]; exact (Q v).end_mem_support⟩
  · intro x y hxy
    have hH : H.Adj x y := hGH hxy
    let d : H.Dart := ⟨(x, y), hH⟩
    have h1 := M.dart_tail (M.dart.symm d).1 (M.dart.symm d).2
    have h2 := M.dart_head (M.dart.symm d).1 (M.dart.symm d).2
    simp only [Prod.mk.eta, Equiv.apply_symm_apply] at h1 h2
    refine ⟨(M.dart.symm d).1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(M.dart.symm d).2, ?_⟩
      rw [← h1]; exact (Q _).end_mem_support
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(M.dart.symm d).2 + 1, ?_⟩
      rw [← h2]; exact (Q _).end_mem_support
  · intro s s' s'' p hp hs' v hv
    rw [Finset.mem_inter] at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    set S : Set (Fin m) := {f | ∃ i : Fin 3, v ∈ (Q (M.corner f i)).support} with hS
    have hc := hFace v
    obtain ⟨w⟩ := hc.preconnected ⟨s, hv.1⟩ ⟨s'', hv.2⟩
    let w' : (M.cotree R).Walk s s'' := w.map (SimpleGraph.Embedding.induce (G := M.cotree R) S).toHom
    have hpq : (⟨p, hp⟩ : (M.cotree R).Path s s'') = w'.toPath :=
      hD.IsAcyclic.path_unique _ _
    have hsub : s' ∈ w'.support := by
      have : s' ∈ (w'.toPath : (M.cotree R).Walk s s'').support := by
        rw [← hpq]; exact hs'
      exact w'.support_toPath_subset_support this
    have hsub' : s' ∈ w.support.map (SimpleGraph.Embedding.induce (G := M.cotree R) S).toHom := by
      rw [← SimpleGraph.Walk.support_map]; exact hsub
    rw [List.mem_map] at hsub'
    obtain ⟨⟨u, hu⟩, _, hu'⟩ := hsub'
    have : u = s' := hu'
    rw [← this]; exact hu
  · intro s
    refine ⟨M.corner s 0, M.corner s 1, M.corner s 2, fun v hv => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨i, hi⟩ := hv
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
