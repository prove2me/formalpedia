-- Prove2me | solution 1 for Sensitivity.fullDegree_imbalance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:01:32.635027+00:00
-- url     : https://prove2.me/submissions/92f8705d-d506-49e5-aaac-0944e1e337b8

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_Sensitivity_Parity
import Theorems.Thm_Sensitivity_fullDegree_paritySigned_sum_ne_zero
import Theorems.Thm_Sensitivity_boolToInt_false
import Theorems.Thm_Sensitivity_boolToInt_true
import Theorems.Thm_Sensitivity_flipBit_apply_ne
import Theorems.Thm_Sensitivity_flipBit_apply_same
import Theorems.Thm_Sensitivity_flipBit_flipBit_same
import Theorems.Thm_Sensitivity_indicator_mem
import Theorems.Thm_Sensitivity_indicator_not_mem
attribute [local simp] Sensitivity.boolToInt_false
attribute [local simp] Sensitivity.boolToInt_true
attribute [local simp] Sensitivity.flipBit_apply_ne
attribute [local simp] Sensitivity.flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_flipBit_same
attribute [local simp] Sensitivity.indicator_mem
attribute [local simp] Sensitivity.indicator_not_mem



set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
theorem _root_.solution (f : BoolFun n) (hn : 0 < n)
    (h : f.moebius Finset.univ ≠ 0) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      2 ^ (n - 1) < (Finset.univ.filter (fun x : Fin n → Bool =>
        f.paritySigned x = c)).card := by
  -- The parity-weighted sum is nonzero
  have hne := fullDegree_paritySigned_sum_ne_zero f hn h
  -- Each paritySigned value is ±1 (since pmOne is ±1 and parity is ±1)
  have hval : ∀ x : Fin n → Bool, f.paritySigned x = 1 ∨ f.paritySigned x = -1 := by
    intro x; unfold BoolFun.paritySigned BoolFun.pmOne parity
    rcases neg_one_pow_eq_or (R := ℤ)
      (Finset.univ.filter (fun i => x i)).card with h | h <;>
      cases f x <;> simp [h]
  -- Let A = {x | paritySigned x = 1}, B = {x | paritySigned x = -1}
  set A := Finset.univ.filter (fun x : Fin n → Bool => f.paritySigned x = 1)
  set B := Finset.univ.filter (fun x : Fin n → Bool => f.paritySigned x = -1)
  -- A ∪ B = univ and they are disjoint
  have hunion : A ∪ B = Finset.univ := by
    ext x; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, A, B]
    exact iff_of_true (hval x) trivial
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hxA hxB
    linarith
  -- ∑ paritySigned = |A| - |B|
  have hsum : ∑ x : Fin n → Bool, f.paritySigned x = ↑A.card - ↑B.card := by
    have hA_sum : ∑ x ∈ A, f.paritySigned x = (A.card : ℤ) := by
      calc ∑ x ∈ A, f.paritySigned x = ∑ _ ∈ A, (1 : ℤ) :=
            Finset.sum_congr rfl (fun x hx => by
              simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx)
        _ = ↑A.card := by simp
    have hB_sum : ∑ x ∈ B, f.paritySigned x = -(↑B.card : ℤ) := by
      calc ∑ x ∈ B, f.paritySigned x = ∑ _ ∈ B, (-1 : ℤ) :=
            Finset.sum_congr rfl (fun x hx => by
              simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx)
        _ = -(↑B.card : ℤ) := by simp
    -- Decompose the sum over univ into A ∪ B
    have key : ∑ x ∈ A ∪ B, f.paritySigned x = ↑A.card - ↑B.card := by
      rw [Finset.sum_union hdisj, hA_sum, hB_sum]; ring
    rwa [hunion] at key
  -- |A| + |B| = 2^n (total number of Boolean vectors)
  have htotal : A.card + B.card = 2 ^ n := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ,
        Fintype.card_pi_const, Fintype.card_bool]
  -- Since sum ≠ 0, one of |A|, |B| must be > 2^(n-1)
  by_cases hA : A.card > 2 ^ (n - 1)
  · exact ⟨1, Or.inl rfl, hA⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    push_neg at hA
    -- Unify the goal's filter expression with B
    show 2 ^ (n - 1) < B.card
    -- hA : A.card ≤ 2^(n-1), htotal : A.card + B.card = 2^n
    -- Need: 2^(n-1) < B.card
    -- Strict inequality: if B.card = 2^(n-1), then A.card = 2^(n-1), sum = 0, contradiction
    suffices hne' : B.card ≠ 2 ^ (n - 1) by
      -- Prove h2pow with concrete expressions, then abstract for omega
      have h2pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
        conv_lhs => rw [show n = (n - 1) + 1 from by omega]
        rw [pow_succ]; ring
      set p := 2 ^ (n - 1)
      omega
    intro heq
    have hA_eq : A.card = 2 ^ (n - 1) := by
      have h2pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
        conv_lhs => rw [show n = (n - 1) + 1 from by omega]
        rw [pow_succ]; ring
      set p := 2 ^ (n - 1)
      omega
    apply hne
    rw [hsum, hA_eq, heq]; push_cast; omega
end Sensitivity
