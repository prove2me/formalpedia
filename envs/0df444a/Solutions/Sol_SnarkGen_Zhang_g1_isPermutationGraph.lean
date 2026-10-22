-- Prove2me | solution 1 for SnarkGen.Zhang.g1_isPermutationGraph
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:56:46.638361+00:00
-- url     : https://prove2.me/submissions/579a4ac8-1516-4059-ab34-0a45b729e625

import Mathlib
import Definitions.Def_SnarkGen_Zhang_g1
import Definitions.Def_SnarkGen_Zhang_IsPermutationGraph

set_option autoImplicit false
open SnarkGen.Zhang

theorem g1_cubic : g1.IsRegularOfDegree 3 := by
  intro v
  revert v
  decide +kernel

def cA : Fin 17 → Fin 34 :=
  ![0, 8, 9, 1, 5, 26, 4, 20, 30, 31, 29, 28, 12, 23, 22, 6, 10]

def cB : Fin 17 → Fin 34 :=
  ![2, 11, 17, 21, 13, 33, 32, 27, 24, 25, 18, 19, 16, 14, 15, 3, 7]

theorem cA_inj : Function.Injective cA := by decide +kernel
theorem cB_inj : Function.Injective cB := by decide +kernel

theorem cA_adj : ∀ i j : Fin 17, g1.Adj (cA i) (cA j) ↔ (SimpleGraph.cycleGraph 17).Adj i j := by
  decide +kernel

theorem cB_adj : ∀ i j : Fin 17, g1.Adj (cB i) (cB j) ↔ (SimpleGraph.cycleGraph 17).Adj i j := by
  decide +kernel

theorem compl_eq : (Set.range cA)ᶜ = Set.range cB := by
  have : ∀ v : Fin 34, (¬ ∃ i, cA i = v) ↔ ∃ j, cB j = v := by decide +kernel
  ext v
  simp only [Set.mem_compl_iff, Set.mem_range]
  exact this v

theorem cyc_of (A : Set (Fin 34)) {inst : Fintype ↥A} (c : Fin 17 → Fin 34)
    (hinj : Function.Injective c) (hA : A = Set.range c)
    (hadj : ∀ i j : Fin 17, g1.Adj (c i) (c j) ↔ (SimpleGraph.cycleGraph 17).Adj i j) :
    @IsCycleGraph ↥A inst (g1.induce A) := by
  subst hA
  let e : (SimpleGraph.cycleGraph 17) ≃g g1.induce (Set.range c) :=
    ⟨Equiv.ofInjective c hinj, by
      intro i j
      simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, Equiv.ofInjective_apply]
      exact hadj i j⟩
  refine ⟨?_, ?_⟩
  · exact e.connected_iff.1 (SimpleGraph.cycleGraph_connected (n := 16))
  · intro v
    obtain ⟨i, rfl⟩ := e.surjective v
    classical
    have h2 : (g1.induce (Set.range c)).degree (e i) = 2 :=
      (e.degree_eq i).trans (SimpleGraph.cycleGraph_degree_three_le (n := 14))
    convert h2

theorem solution : IsPermutationGraph g1 := by
  refine ⟨?_, Set.range cA, ?_, ?_⟩
  · convert g1_cubic
  · exact cyc_of _ cA cA_inj rfl cA_adj
  · exact cyc_of _ cB cB_inj compl_eq cB_adj
