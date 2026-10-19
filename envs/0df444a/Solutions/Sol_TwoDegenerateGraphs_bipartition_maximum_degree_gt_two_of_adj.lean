-- Prove2me | solution 1 for TwoDegenerateGraphs.bipartition_maximum_degree_gt_two_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/bbc87921-ec2e-4c83-a508-57697796a12a

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open Classical
namespace TwoDegenerateGraphs
theorem _root_.solution
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {u v : V}
    (hadj : G.Adj u v)
    (hu : 2 < G.degree u) (hv : 2 < G.degree v) :
    ∀ coloring : G.Coloring (Fin 2), ∀ side : Fin 2,
      2 < (Finset.univ.filter
        (fun vertex : V => coloring vertex = side)).sup
        (fun vertex => G.degree vertex) := by
  classical
  intro coloring side
  have hwitness :
      ∃ vertex : V,
        coloring vertex = side ∧ 2 < G.degree vertex := by
    by_cases hcolor : coloring u = side
    · exact ⟨u, hcolor, hu⟩
    · refine ⟨v, ?_, hv⟩
      have hproper : coloring u ≠ coloring v := coloring.valid hadj
      apply Fin.ext
      have hu_lt := (coloring u).isLt
      have hv_lt := (coloring v).isLt
      have hside_lt := side.isLt
      omega
  obtain ⟨vertex, hcolor, hdegree⟩ := hwitness
  have hmember :
      vertex ∈ Finset.univ.filter
        (fun candidate : V => coloring candidate = side) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ vertex, hcolor⟩
  exact lt_of_lt_of_le hdegree
    (Finset.le_sup (f := fun candidate => G.degree candidate) hmember)
end TwoDegenerateGraphs
