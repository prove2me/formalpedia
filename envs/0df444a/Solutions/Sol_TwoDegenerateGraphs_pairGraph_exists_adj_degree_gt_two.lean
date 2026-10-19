-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraph_exists_adj_degree_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/80c4def3-76db-4dbb-9707-81cf32ed174f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraph_parent_child_adj
import Theorems.Thm_TwoDegenerateGraphs_degree_gt_two_of_three_neighbors

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open Classical
namespace TwoDegenerateGraphs
theorem _root_.solution
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∃ u v : PairVertex baseSize depth,
      (pairParentSystem baseSize depth).graph.Adj u v ∧
      2 < (pairParentSystem baseSize depth).graph.degree u ∧
      2 < (pairParentSystem baseSize depth).graph.degree v := by
  classical
  let a : PairLayer baseSize 0 := ⟨0, by omega⟩
  let b : PairLayer baseSize 0 := ⟨1, by omega⟩
  let c : PairLayer baseSize 0 := ⟨2, by omega⟩
  let d : PairLayer baseSize 0 := ⟨3, by omega⟩
  letI pairDecidableEq : DecidableEq (PairLayer baseSize 0) := Classical.decEq _
  have hab : a ≠ b := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 1 at hval
    omega
  have hac : a ≠ c := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 2 at hval
    omega
  have had : a ≠ d := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 3 at hval
    omega
  have hbc : b ≠ c := by
    intro heq
    have hval := congrArg Fin.val heq
    change 1 = 2 at hval
    omega
  have hbd : b ≠ d := by
    intro heq
    have hval := congrArg Fin.val heq
    change 1 = 3 at hval
    omega
  have hcd : c ≠ d := by
    intro heq
    have hval := congrArg Fin.val heq
    change 2 = 3 at hval
    omega
  let ab : PairLayer baseSize 1 :=
    ⟨{a, b}, Finset.card_pair hab⟩
  let ac : PairLayer baseSize 1 :=
    ⟨{a, c}, Finset.card_pair hac⟩
  let ad : PairLayer baseSize 1 :=
    ⟨{a, d}, Finset.card_pair had⟩
  have habac : ab ≠ ac := by
    intro heq
    have hmem : b ∈ ab.val := by
      change b ∈ ({a, b} : Finset (PairLayer baseSize 0))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [heq] at hmem
    change b ∈ ({a, c} : Finset (PairLayer baseSize 0)) at hmem
    rcases Finset.mem_insert.mp hmem with hba | hbc'
    · exact hab hba.symm
    · exact hbc (Finset.mem_singleton.mp hbc')
  have habad : ab ≠ ad := by
    intro heq
    have hmem : b ∈ ab.val := by
      change b ∈ ({a, b} : Finset (PairLayer baseSize 0))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [heq] at hmem
    change b ∈ ({a, d} : Finset (PairLayer baseSize 0)) at hmem
    rcases Finset.mem_insert.mp hmem with hba | hbd'
    · exact hab hba.symm
    · exact hbd (Finset.mem_singleton.mp hbd')
  have hacad : ac ≠ ad := by
    intro heq
    have hmem : c ∈ ac.val := by
      change c ∈ ({a, c} : Finset (PairLayer baseSize 0))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self c)
    rw [heq] at hmem
    change c ∈ ({a, d} : Finset (PairLayer baseSize 0)) at hmem
    rcases Finset.mem_insert.mp hmem with hca | hcd'
    · exact hac hca.symm
    · exact hcd (Finset.mem_singleton.mp hcd')
  let abc : PairLayer baseSize 2 :=
    ⟨{ab, ac}, Finset.card_pair habac⟩
  let va : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 0 (by omega) a
  let vb : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 0 (by omega) b
  let vab : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 1 (by omega) ab
  let vac : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 1 (by omega) ac
  let vad : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 1 (by omega) ad
  let vabc : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 2 (by omega) abc
  let G : SimpleGraph (PairVertex baseSize depth) :=
    (pairParentSystem baseSize depth).graph
  have ha_mem_ab : a ∈ ab.val := by
    change a ∈ ({a, b} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_self a {b}
  have hb_mem_ab : b ∈ ab.val := by
    change b ∈ ({a, b} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have ha_mem_ac : a ∈ ac.val := by
    change a ∈ ({a, c} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_self a {c}
  have ha_mem_ad : a ∈ ad.val := by
    change a ∈ ({a, d} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_self a {d}
  have hab_a : G.Adj vab va := by
    simpa only [G, vab, va] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ab a ha_mem_ab
  have hab_b : G.Adj vab vb := by
    simpa only [G, vab, vb] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ab b hb_mem_ab
  have hac_a : G.Adj vac va := by
    simpa only [G, vac, va] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ac a ha_mem_ac
  have had_a : G.Adj vad va := by
    simpa only [G, vad, va] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ad a ha_mem_ad
  have habc_ab : G.Adj vabc vab := by
    simpa only [G, vabc, vab] using
      pairGraph_parent_child_adj baseSize depth 1
        (by omega) abc ab (by
          change ab ∈ ({ab, ac} : Finset (PairLayer baseSize 1))
          exact Finset.mem_insert_self ab {ac})
  have hab_vac : vab ≠ vac := by
    intro heq
    apply habac
    exact (pairLayerEmbedding baseSize depth 1 (by omega)).inj' heq
  have hab_vad : vab ≠ vad := by
    intro heq
    apply habad
    exact (pairLayerEmbedding baseSize depth 1 (by omega)).inj' heq
  have hac_vad : vac ≠ vad := by
    intro heq
    apply hacad
    exact (pairLayerEmbedding baseSize depth 1 (by omega)).inj' heq
  have ha_b : va ≠ vb := by
    intro heq
    have hfin := (pairLayerEmbedding baseSize depth 0 (by omega)).inj' heq
    have hval := congrArg Fin.val hfin
    simp [a, b] at hval
  have ha_abc : va ≠ vabc := by
    intro heq
    have hlevel := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val) heq
    change 0 = 2 at hlevel
    omega
  have hb_abc : vb ≠ vabc := by
    intro heq
    have hlevel := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val) heq
    change 0 = 2 at hlevel
    omega
  have ha_degree : 2 < G.degree va :=
    degree_gt_two_of_three_neighbors G va vab vac vad
      hab_a.symm hac_a.symm had_a.symm
      hab_vac hab_vad hac_vad
  have hab_degree : 2 < G.degree vab :=
    degree_gt_two_of_three_neighbors G vab va vb vabc
      hab_a hab_b habc_ab.symm ha_b ha_abc hb_abc
  exact ⟨va, vab, hab_a.symm, ha_degree, hab_degree⟩
end TwoDegenerateGraphs
