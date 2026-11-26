-- Prove2me | solution 1 for QuarterSumLadder.two_mul_card_filter_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:00:23.536009+00:00
-- url     : https://prove2.me/submissions/a7fb5135-35d5-4f28-9cae-21466d367cfd

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {S : Finset (ZMod p)} (P : ZMod p → Prop) [DecidablePred P]
    (hS : ∀ x ∈ S, -x ∈ S) (hP : ∀ x ∈ S, (P (-x) ↔ ¬ P x)) :
    2 * (S.filter P).card = S.card := by
  have h : (S.filter P).card = (S.filter fun x => ¬ P x).card := by
    refine card_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨hS x hx.1, fun h => ((hP x hx.1).1 h) hx.2⟩
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨hS x hx.1, (hP x hx.1).2 hx.2⟩
    · intro x _; simp
    · intro x _; simp
  have := card_filter_add_card_filter_not (s := S) (p := P)
  omega
end QuarterSumLadder
