-- Prove2me | solution 1 for RamseyLib.es_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:15:53.613098+00:00
-- url     : https://prove2.me/submissions/3964b3f0-a58d-43e2-a00d-50e9d4b9fdfd

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib
namespace RamseyLib
theorem _root_.solution {V : Type*} (G : SimpleGraph V) :
    ∀ (s t : ℕ) (S : Finset V), (s + t).choose s ≤ S.card →
      (∃ T ⊆ S, G.IsNClique (s + 1) T) ∨ (∃ T ⊆ S, Gᶜ.IsNClique (t + 1) T) := by
  classical
  intro s
  induction s with
  | zero =>
    intro t S hS
    rw [Nat.choose_zero_right, Finset.one_le_card] at hS
    obtain ⟨v, hv⟩ := hS
    exact Or.inl ⟨{v}, by simpa using hv, by simp⟩
  | succ s ihs =>
    intro t
    induction t with
    | zero =>
      intro S hS
      rw [add_zero, Nat.choose_self, Finset.one_le_card] at hS
      obtain ⟨v, hv⟩ := hS
      exact Or.inr ⟨{v}, by simpa using hv, by simp⟩
    | succ t iht =>
      intro S hS
      have hpos : 0 < S.card := lt_of_lt_of_le (Nat.choose_pos (by omega)) hS
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      set N := (S.erase v).filter (fun w => G.Adj v w) with hN
      set M := (S.erase v).filter (fun w => ¬ G.Adj v w) with hM
      have hcard : N.card + M.card = S.card - 1 := by
        rw [hN, hM, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
      have hpas : (s + 1 + (t + 1)).choose (s + 1) =
          (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := by
        rw [show s + 1 + (t + 1) = (s + 1 + t) + 1 by omega, Nat.choose_succ_succ,
          show s + 1 + t = s + (t + 1) by omega]
      have hNS : N ⊆ S := fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ hx)
      have hMS : M ⊆ S := fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ hx)
      by_cases hNc : (s + (t + 1)).choose s ≤ N.card
      · rcases ihs (t + 1) N hNc with ⟨T, hT, hc⟩ | ⟨T, hT, hc⟩
        · left
          refine ⟨insert v T, Finset.insert_subset hv (hT.trans hNS), ?_⟩
          refine hc.insert fun b hb => ?_
          exact (Finset.mem_filter.1 (hT hb)).2
        · exact Or.inr ⟨T, hT.trans hNS, hc⟩
      · have hMc : (s + 1 + t).choose (s + 1) ≤ M.card := by omega
        rcases iht M hMc with ⟨T, hT, hc⟩ | ⟨T, hT, hc⟩
        · exact Or.inl ⟨T, hT.trans hMS, hc⟩
        · right
          refine ⟨insert v T, Finset.insert_subset hv (hT.trans hMS), ?_⟩
          refine hc.insert fun b hb => ?_
          have hb' := Finset.mem_filter.1 (hT hb)
          rw [compl_adj]
          exact ⟨fun h => Finset.ne_of_mem_erase hb'.1 h.symm, hb'.2⟩
end RamseyLib
