-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition_family__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1__p2m_94e5824a_c757_4689_bf4f_99cc2f2adc56_a1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T23:35:04.497776+00:00
-- url     : https://prove2.me/submissions/5e9f8dcd-b288-43a8-9046-6059a796db30

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem membership_of_finset_eq {V : Type} [Fintype V] (S : Set V) [DecidablePred (· ∈ S)]
    (W : Finset V) (v : V) (hc : S.toFinset = W) (hv : v ∈ W) : v ∈ S := by
  classical
  have hv' : v ∈ S.toFinset := by
    rw [hc]
    exact hv
  simpa using hv'

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W) ∧
      (∀ W ∈ parts, (M.induce (W : Set V)).Connected) ∧
      (∀ u v : V, M.Adj u v → ∃ W ∈ parts, u ∈ W ∧ v ∈ W) := by
  classical
  let parts : Finset (Finset V) :=
    Finset.univ.image fun c : M.ConnectedComponent => c.supp.toFinset
  refine ⟨parts, ?_, ?_, ?_⟩
  · intro v
    refine ⟨(M.connectedComponentMk v).supp.toFinset, ?_, ?_⟩
    · simp [parts]
    · intro W hW
      rcases Finset.mem_image.mp hW.1 with ⟨c, -, hc⟩
      have hv : v ∈ c.supp := membership_of_finset_eq c.supp W v hc hW.2
      have hcomp : M.connectedComponentMk v = c :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mp hv
      rw [← hc, hcomp]
  · intro W hW
    rcases Finset.mem_image.mp hW with ⟨c, -, rfl⟩
    rw [Set.coe_toFinset]
    exact c.connected_toSimpleGraph
  · intro u v hadj
    refine ⟨(M.connectedComponentMk u).supp.toFinset, ?_, ?_, ?_⟩
    · simp [parts]
    · simp
    · simp only [Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm

