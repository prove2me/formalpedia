-- Prove2me | solution 1 for P2M_DeciSigma1_Holes_Tail_suffixChain_getElem__eq_of_mem_b81ca86b8910
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:52.086882+00:00
-- url     : https://prove2.me/submissions/cf294867-6d81-45cb-af9b-7774e40245e2

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_prefix_drop_iff
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_pairwise
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {t : List α} {b b' : ℕ} {bs : List ℕ}
    (h : SuffixChain t (b :: bs)) (hb' : b' ∈ b :: bs) (hle : b' ≤ t.length) :
    b ≤ b' ∧ ∀ j < b, t[t.length - b' + j]? = t[t.length - b + j]? := by
  rcases List.mem_cons.mp hb' with rfl | hmem
  · exact ⟨le_rfl, fun _ _ => rfl⟩
  obtain ⟨hlt, -, hpre⟩ := (List.pairwise_cons.mp h.pairwise).1 b' hmem
  unfold suffixOfLength at hpre
  rw [prefix_drop_iff (Nat.sub_le _ _)] at hpre
  refine ⟨hlt.le, fun j hj => ?_⟩
  rw [hpre.2 j (by simp; omega), List.getElem?_drop]
end DeciSigma1.Holes.Tail
