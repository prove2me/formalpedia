-- Prove2me | solution 1 for PathsTreesFlowers.Invariance.theorem_6_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T07:57:09.691986+00:00
-- url     : https://prove2.me/submissions/b89fd144-bfe6-49b3-8e77-d4572f2adf63

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Partition.Finpartition
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config
import Theorems.Thm_PathsTreesFlowers_Invariance_outer_exposed_6_5
import Theorems.Thm_PathsTreesFlowers_Invariance_exposed_only_outer_6_6
import Theorems.Thm_PathsTreesFlowers_Invariance_theorem_6_2_b
import Theorems.Thm_PathsTreesFlowers_Invariance_theorem_6_2_c

open PathsTreesFlowers.Invariance

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    (∀ v : V, v ∈ outerSet C ↔ ∃ M' : Finset E, PathsTreesFlowers.Duality.IsMaxMatching G M' ∧ PathsTreesFlowers.Duality.IsExposed G M' v) ∧
    (∀ v : V, v ∈ innerSet C ↔
      v ∉ outerSet C ∧ ∃ u ∈ outerSet C, ∃ e : E, G.ends e = s(u, v)) ∧
    (∀ u v : V, C.P.part u = C.P.part v ↔
      (u = v ∨ (u ∈ outerSet C ∧ v ∈ outerSet C ∧
        Relation.ReflTransGen
          (fun x y => x ∈ outerSet C ∧ y ∈ outerSet C ∧ ∃ e : E, G.ends e = s(x, y)) u v))) := by
  refine ⟨fun v => ⟨outer_exposed_6_5 G M C v, ?_⟩, theorem_6_2_b G M C, theorem_6_2_c G M C⟩
  rintro ⟨M', hM', hexp⟩
  exact exposed_only_outer_6_6 G M C M' v hM' hexp
