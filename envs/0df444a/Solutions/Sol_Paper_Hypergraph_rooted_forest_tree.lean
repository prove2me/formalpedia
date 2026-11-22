-- Prove2me | solution 1 for Paper.Hypergraph.rooted_forest_tree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:32.423551+00:00
-- url     : https://prove2.me/submissions/7f912ba6-17f3-42f9-9fd1-cb1003146711

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_forest_acyclic

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {I : Type*} {V : I → Type*}
    (G : ∀ i, SimpleGraph (V i)) (hG : ∀ i, (G i).IsTree)
    (root : ∀ i, V i) (o : I) :
    ∃ F : SimpleGraph (Sigma V), F.IsTree ∧ forestGraph G ≤ F ∧
      ∀ i, i ≠ o → F.Adj ⟨o, root o⟩ ⟨i, root i⟩ := by
  classical
  let c : Sigma V := ⟨o, root o⟩
  let q : I → Sigma V := fun i => ⟨i, root i⟩
  let A := forestGraph G
  let M := A ⊔ ⨆ i, SimpleGraph.edge c (q i)
  have hedge (i : I) (hi : i ≠ o) : M.Adj c (q i) := by
    apply Or.inr
    rw [SimpleGraph.iSup_adj]
    refine ⟨i, (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩⟩
    intro heq
    exact hi (congrArg Sigma.fst heq).symm
  have hinside (i : I) (a b : V i) : M.Reachable ⟨i, a⟩ ⟨i, b⟩ := by
    let f : G i →g A := {
      toFun := fun v => ⟨i, v⟩
      map_rel' := fun h => ⟨rfl, h⟩ }
    exact (((hG i).connected a b).map f).mono le_sup_left
  have htoc (a : Sigma V) : M.Reachable a c := by
    have hh := hinside a.1 a.2 (root a.1)
    by_cases hi : a.1 = o
    · cases a with
      | mk i v =>
        dsimp at hi
        subst i
        exact hh
    · exact hh.trans (hedge a.1 hi).symm.reachable
  letI : Nonempty (Sigma V) := ⟨c⟩
  have hM : M.Connected := ⟨fun a b => (htoc a).trans (htoc b).symm⟩
  obtain ⟨F, hAF, hFM, hF⟩ := hM.exists_isTree_le_of_le_of_isAcyclic
    (H := A) le_sup_left (forest_acyclic G (fun i => (hG i).isAcyclic))
  refine ⟨F, hF, hAF, ?_⟩
  intro i hi
  by_contra hn
  have hstay {a b : Sigma V} (ha : a.1 = i) (hab : F.Adj a b) : b.1 = i := by
    rcases hFM hab with hab' | hab'
    · obtain ⟨heq, _⟩ := hab'
      exact heq.symm.trans ha
    · rw [SimpleGraph.iSup_adj] at hab'
      obtain ⟨j, hj⟩ := hab'
      rcases ((SimpleGraph.edge_adj _ _ _ _).mp hj).1 with ⟨hac, hbq⟩ | ⟨haq, hbc⟩
      · exact (hi (ha.symm.trans (congrArg Sigma.fst hac))).elim
      · have hji : j = i := (congrArg Sigma.fst haq).symm.trans ha
        subst j
        have hh : F.Adj (q i) c := by simpa only [haq, hbc] using hab
        exact (hn hh.symm).elim
  have hpath {a b : Sigma V} (p : F.Walk a b) (ha : a.1 = i) : b.1 = i := by
    induction p with
    | nil => exact ha
    | cons hab p ih => exact ih (hstay ha hab)
  exact hi (hpath (hF.connected (q i) c).some rfl).symm
end Paper.Hypergraph
