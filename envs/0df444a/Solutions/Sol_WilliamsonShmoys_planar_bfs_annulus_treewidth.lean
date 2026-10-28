-- Prove2me | solution 1 for WilliamsonShmoys.planar_bfs_annulus_treewidth
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T21:51:44.04271+00:00
-- url     : https://prove2.me/submissions/601ac656-4bec-4e78-8f4c-0de2cf2c27e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_WilliamsonShmoys_coherent_shortest_root_paths
import Theorems.Thm_WilliamsonShmoys_planar_coherent_root_path_decomposition

set_option autoImplicit false

/-- Distances from the initial vertex distinguish vertices on a geodesic.
This uses shortestness, not just simplicity of the walk. -/
theorem WilliamsonShmoys.root_dist_injOn_geodesic_support
    {V : Type} {G : SimpleGraph V} {root dest : V}
    (p : G.Walk root dest) (hp : p.length = G.dist root dest) :
    Set.InjOn (G.dist root) {v : V | v ∈ p.support} := by
  classical
  intro u hu v hv huv
  have hu' : (p.takeUntil u hu).length = G.dist root u :=
    SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hu)
  have hv' : (p.takeUntil v hv).length = G.dist root v :=
    SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hv)
  calc
    u = p.getVert (p.takeUntil u hu).length :=
      (p.getVert_length_takeUntil hu).symm
    _ = p.getVert (p.takeUntil v hv).length := by rw [hu', hv', huv]
    _ = v := p.getVert_length_takeUntil hv

/-
Reduction by rooted paths rather than contraction.

The two imported Open children are separate structural facts:
* coherent_shortest_root_paths is the BFS spanning-tree construction and
  has no planarity hypothesis;
* planar_coherent_root_path_decomposition is the plane tree-cotree
  construction for ANY coherent simple root paths and has no metric or
  annulus-width hypothesis.

For the second child, restrict the drawing to the root component, complete
it to a plane triangulation while retaining the rooted spanning tree, and
use the dual edges complementary to that tree. They form a tree on faces.
The bag for a triangular face is the union of its three root paths.
The standard fundamental-cycle argument proves the running-intersection
condition. Components of size one or two are handled by a single bag;
the three endpoints in the child need not be distinct.

Source: Dujmovic, Morin, Wood, Layered separators in minor-closed graph
classes with applications, JCTB 127 (2017), Section 3, proof of Theorem 12
(specialize genus to zero); the same tree-cotree construction is recalled
in Illingworth, Scott, Wood, Product structure of graphs with an excluded
minor, proof of Theorem 19. These are mathematical sources, not existing
Lean proofs. The topological drawing-to-plane-map and triangulation work
remains in the second child.

Below, restricting the bags preserves every tree-decomposition axiom.
On any shortest root path, distance minus lo injects the annulus vertices
into range k. Thus each restricted bag has at most 3*k vertices, even
though the target permits 3*k+1. No lo<=hi assumption is introduced;
if hi<lo the new bags are empty automatically.
-/

theorem solution {n : Nat} (G : SimpleGraph (Fin n)) (root : Fin n)
    (k : Nat) (lo hi : Nat) (hwidth : hi - lo < k)
    (hG : WilliamsonShmoys.HasPlanarDrawing G) :
    RobertsonSeymour1986.GM5.TreewidthLE
      (G.induce {x : Fin n |
        G.Reachable root x ∧ lo ≤ G.dist root x ∧ G.dist root x ≤ hi})
      (3 * k) := by
  classical
  obtain ⟨P, hP, hprefix⟩ :=
    WilliamsonShmoys.coherent_shortest_root_paths G root
  obtain ⟨T, hT, t, X, hdec, hbags⟩ :=
    WilliamsonShmoys.planar_coherent_root_path_decomposition
      G root hG P (fun v => (hP v).1) hprefix
  letI : Fintype T := hT
  let C := {x : Fin n // G.Reachable root x}
  let A := {x : Fin n //
    G.Reachable root x ∧ lo ≤ G.dist root x ∧ G.dist root x ≤ hi}
  let f : A → C := fun v => ⟨v.val, v.property.1⟩
  let Y : T → Finset A := fun s => Finset.univ.filter (fun v => f v ∈ X s)
  have memY (s : T) (v : A) : v ∈ Y s ↔ f v ∈ X s := by
    simp [Y]
  refine ⟨T, hT, t, Y, ?_, ?_⟩
  · refine ⟨hdec.1, ?_, ?_, ?_⟩
    · intro v
      obtain ⟨s, hs⟩ := hdec.2.1 (f v)
      exact ⟨s, (memY s v).2 hs⟩
    · intro u v huv
      have huv' : (G.induce {x : Fin n | G.Reachable root x}).Adj (f u) (f v) :=
        huv
      obtain ⟨s, hu, hv⟩ := hdec.2.2.1 (f u) (f v) huv'
      exact ⟨s, (memY s u).2 hu, (memY s v).2 hv⟩
    · intro s s' s'' p hp hs' v hv
      apply (memY s' v).2
      exact hdec.2.2.2 s s' s'' p hp hs'
        (Finset.mem_inter.mpr
          ⟨(memY s v).1 (Finset.mem_inter.mp hv).1,
           (memY s'' v).1 (Finset.mem_inter.mp hv).2⟩)
  · let Z : C → Finset A :=
      fun a => Finset.univ.filter (fun v => v.val ∈ (P a).support)
    have hZ (a : C) : (Z a).card ≤ k := by
      calc
        (Z a).card ≤ (Finset.range k).card := by
          apply Finset.card_le_card_of_injOn
            (fun v : A => G.dist root v.val - lo)
          · intro v hv
            apply Finset.mem_range.mpr
            change G.dist root v.val - lo < k
            have hlo := v.property.2.1
            have hhi := v.property.2.2
            omega
          · intro v hv w hw heq
            change G.dist root v.val - lo = G.dist root w.val - lo at heq
            have hvP : v.val ∈ (P a).support := (Finset.mem_filter.mp hv).2
            have hwP : w.val ∈ (P a).support := (Finset.mem_filter.mp hw).2
            have hdist : G.dist root v.val = G.dist root w.val := by
              have hvlo := v.property.2.1
              have hwlo := w.property.2.1
              omega
            apply Subtype.ext
            exact WilliamsonShmoys.root_dist_injOn_geodesic_support
              (P a) (hP a).2 hvP hwP hdist
        _ = k := Finset.card_range k
    intro s
    obtain ⟨a, b, c, hcover⟩ := hbags s
    have hsubset : Y s ⊆ (Z a ∪ Z b) ∪ Z c := by
      intro v hv
      simp only [Finset.mem_union]
      rcases hcover (f v) ((memY s v).1 hv) with ha | hb | hc
      · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩))
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩))
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    calc
      (Y s).card ≤ ((Z a ∪ Z b) ∪ Z c).card := Finset.card_le_card hsubset
      _ ≤ (Z a ∪ Z b).card + (Z c).card := Finset.card_union_le _ _
      _ ≤ ((Z a).card + (Z b).card) + (Z c).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ 3 * k + 1 := by
        have ha := hZ a
        have hb := hZ b
        have hc := hZ c
        omega
