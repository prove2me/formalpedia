-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.exists_two_adj_of_connected_deletions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:23:46.191803+00:00
-- url     : https://prove2.me/submissions/b9958d15-48e4-435a-bb52-0f387daf55c7

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
theorem _root_.solution {G : SimpleGraph α}
    (hcard : 3 ≤ Fintype.card α) (hG : G.Connected)
    (hdel : ∀ x, (G.induce ({x}ᶜ : Set α)).Connected) (c : α) :
    ∃ u v : α, G.Adj c u ∧ G.Adj c v ∧ u ≠ v := by
  classical
  have hex (s : Finset α) (hs : s.card ≤ 2) : ∃ d, d ∉ s := by
    by_contra! hall
    have heq := Finset.eq_univ_of_forall hall
    rw [heq, Finset.card_univ] at hs
    omega
  obtain ⟨d, hd⟩ := hex {c} (by simp)
  have hcd : c ≠ d := by simpa [eq_comm] using hd
  obtain ⟨p⟩ := hG c d
  let u := p.snd
  have hcu : G.Adj c u := p.adj_snd (p.not_nil_of_ne hcd)
  obtain ⟨e, he⟩ := hex {c, u} Finset.card_le_two
  have hec : e ≠ c := fun hec => he (by simp [hec])
  have heu : e ≠ u := by
    exact fun heu => he (by simp [heu])
  let c' : ↥({u}ᶜ : Set α) := ⟨c, by simpa using hcu.ne⟩
  let e' : ↥({u}ᶜ : Set α) := ⟨e, by simpa using heu⟩
  obtain ⟨q⟩ := hdel u c' e'
  have hc'e' : c' ≠ e' := fun h => hec (congrArg Subtype.val h).symm
  have hcv : G.Adj c (q.snd : α) := q.adj_snd (q.not_nil_of_ne hc'e')
  refine ⟨u, q.snd, hcu, hcv, ?_⟩
  intro huv
  have hvu : (q.snd : α) ≠ u := q.snd.property
  exact hvu huv.symm
end WrittenOnTheWallII.GraphConjecture84
