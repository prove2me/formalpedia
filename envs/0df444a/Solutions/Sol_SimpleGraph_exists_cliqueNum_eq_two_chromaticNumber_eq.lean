-- Prove2me | solution 1 for SimpleGraph.exists_cliqueNum_eq_two_chromaticNumber_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:15:08.560159+00:00
-- url     : https://prove2.me/submissions/ba3d7efa-4d83-46b9-a37b-dce862914d41

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.SplitIfs
public import Definitions.Def_Erdos627_Mycielski
public import Theorems.Thm_SimpleGraph_chromaticNumber_mycielski
public import Theorems.Thm_SimpleGraph_CliqueFree_cliqueNum_le_two
public import Theorems.Thm_SimpleGraph_cliqueNum_mycielski
public import Theorems.Thm_SimpleGraph_cliqueNum_map_equiv
public import Theorems.Thm_SimpleGraph_chromaticNumber_map_equiv

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
variable {V : Type*}
variable {G : SimpleGraph V} {α : Type*} {k : ℕ}
variable {W : Type*}
namespace SimpleGraph
theorem _root_.solution (k : ℕ) (hk : 2 ≤ k) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.cliqueNum = 2 ∧ G.chromaticNumber = (k : ℕ∞) := by
  classical
  have hex (j : ℕ) : ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (G : SimpleGraph V),
      G.CliqueFree 3 ∧ G.cliqueNum = 2 ∧ G.chromaticNumber = ((j + 2 : ℕ) : ℕ∞) := by
    induction j with
    | zero =>
      refine ⟨Fin 2, inferInstance, inferInstance, ⊤, ?_, ?_, by simp⟩
      · exact cliqueFree_of_chromaticNumber_lt (by simp; decide)
      · refine Nat.le_antisymm (CliqueFree.cliqueNum_le_two (cliqueFree_of_chromaticNumber_lt (by simp; decide))) ?_
        have hpair : (⊤ : SimpleGraph (Fin 2)).IsClique (Finset.univ : Finset (Fin 2)) :=
          fun _ _ _ _ h => h
        simpa using hpair.card_le_cliqueNum
    | succ j ih =>
      obtain ⟨V, hV, hne, G, htri, _, hχ⟩ := ih
      let := hV
      let := hne
      refine ⟨Option (V ⊕ V), inferInstance, inferInstance, G.mycielski,
        htri.mycielski, cliqueNum_mycielski htri, ?_⟩
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 2] using
        chromaticNumber_mycielski hχ
  obtain ⟨V, hV, _, G, _, hω, hχ⟩ := hex (k - 2)
  let := hV
  refine ⟨Fintype.card V, G.map (Fintype.equivFin V), ?_, ?_⟩
  · simpa only [cliqueNum_map_equiv] using hω
  · simpa only [chromaticNumber_map_equiv, Nat.sub_add_cancel hk] using hχ
end SimpleGraph
