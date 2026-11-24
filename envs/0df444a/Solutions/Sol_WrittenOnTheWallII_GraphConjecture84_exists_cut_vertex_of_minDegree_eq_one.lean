-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.exists_cut_vertex_of_minDegree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:09.179122+00:00
-- url     : https://prove2.me/submissions/ecb4e7b3-8d91-4e3e-b4c9-3a843fb2fb50

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} [DecidableRel G.Adj]
    [Nonempty α] (hδ : G.minDegree = 1) (hcard : 3 ≤ Fintype.card α) :
    ∃ v, ¬ (G.induce ({v}ᶜ : Set α)).Connected := by
  classical
  obtain ⟨u, hu⟩ := G.exists_minimal_degree_vertex
  have hdu : G.degree u = 1 := hu.symm.trans hδ
  obtain ⟨v, huv, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hdu
  have hw : ∃ w : α, w ≠ u ∧ w ≠ v := by
    by_contra! hn
    have hsub : (Finset.univ : Finset α) ⊆ {u, v} := by
      intro w _
      by_cases hwu : w = u
      · simp [hwu]
      · simp [hn w hwu]
    have hle := Finset.card_le_card hsub
    have hpair : ({u, v} : Finset α).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ] at hle
    omega
  obtain ⟨w, hwu, hwv⟩ := hw
  refine ⟨v, ?_⟩
  intro hc
  let u' : ↥({v}ᶜ : Set α) := ⟨u, by simpa using huv.ne⟩
  let w' : ↥({v}ᶜ : Set α) := ⟨w, by simpa using hwv⟩
  obtain ⟨p⟩ := hc u' w'
  have hne : u' ≠ w' := by
    intro heq
    exact hwu (congrArg Subtype.val heq).symm
  have hadj : G.Adj u (p.snd : α) := p.adj_snd (p.not_nil_of_ne hne)
  have heq : (p.snd : α) = v := huniq _ hadj
  have hmem := p.snd.property
  simpa [heq] using hmem
end WrittenOnTheWallII.GraphConjecture84
