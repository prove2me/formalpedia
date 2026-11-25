-- Prove2me | solution 1 for SimpleGraph.exists_balanced_orientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:04:55.671529+00:00
-- url     : https://prove2.me/submissions/6cf4aa28-c1bb-4d2e-99ef-d2a5714e0759

module
public import Definitions.Def_Euler_Trail
public import Definitions.Def_Euler_Orientation
public import Theorems.Thm_SimpleGraph_exists_larger_balanced
public import Theorems.Thm_SimpleGraph_card_le_of_edgeInj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (heven : ∀ v, Even (G.degree v)) :
    ∃ Ds : Finset G.Dart, EdgeInj Ds ∧ Balanced Ds ∧
      ∀ e ∈ G.edgeSet, ∃ d ∈ Ds, d.edge = e := by
  suffices key : ∀ n, ∀ Ds : Finset G.Dart, EdgeInj Ds → Balanced Ds →
      G.edgeFinset.card - Ds.card = n → ∃ Ds' : Finset G.Dart, EdgeInj Ds' ∧ Balanced Ds' ∧
        ∀ e ∈ G.edgeSet, ∃ d ∈ Ds', d.edge = e by
    exact key _ ∅ (by simp [EdgeInj]) (by simp [Balanced]) rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Ds hinj hbal hn
  by_cases hcov : ∀ e ∈ G.edgeSet, ∃ d ∈ Ds, d.edge = e
  · exact ⟨Ds, hinj, hbal, hcov⟩
  push Not at hcov
  obtain ⟨e, he, hnot⟩ := hcov
  induction e using Sym2.ind with
  | _ x y₀ =>
  obtain ⟨Ds', hinj', hbal', -, hlt⟩ := exists_larger_balanced heven hinj hbal he hnot
  have h1 := card_le_of_edgeInj hinj'
  exact ih _ (by omega) Ds' hinj' hbal' rfl
end SimpleGraph
