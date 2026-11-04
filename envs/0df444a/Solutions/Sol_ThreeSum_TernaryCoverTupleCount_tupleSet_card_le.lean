-- Prove2me | solution 1 for ThreeSum.TernaryCoverTupleCount.tupleSet_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:49.893747+00:00
-- url     : https://prove2.me/submissions/4f2b69ae-b293-4110-949e-be511d175070

import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
import Mathlib.Data.Fin.Tuple.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverTupleCount
import Theorems.Thm_ThreeSum_TernaryCoverTupleCount_tuple_split_card
import Theorems.Thm_ThreeSum_TernaryCoverPairStep_pair_step_count
import Theorems.Thm_ThreeSum_TernaryCoverPairStep_rank_increment


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverTupleCount
open Finset TernaryCoverRankFibers TernaryCoverPairStep
variable {K E ι : Type*} [Field K] [Fintype E] [Fintype ι] [DecidableEq K]
namespace ThreeSum.TernaryCoverTupleCount
theorem _root_.solution (left right : E → ι → K) (P : ℕ)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hE : Fintype.card E ≤ P ^ 2)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : ι → K,
      (projectionFiber left right β γ q).card ≤ P) :
    ∀ n (S : Submodule K (Fin n → K × K)),
      (tupleSet left right n S).card ≤ P ^ Module.finrank K S := by
  classical
  intro n
  induction n with
  | zero =>
    intro S
    have hr : Module.finrank K S = 0 := by
      have h := Submodule.finrank_le S
      have hamb : Module.finrank K (Fin 0 → K × K) = 0 := by
        rw [Module.finrank_pi_fintype]
        simp
      rw [hamb] at h
      omega
    rw [hr, pow_zero]
    exact (card_le_card (filter_subset ..)).trans_eq (by simp)
  | succ n ih =>
    intro S
    let T := S.map (splitRows (K := K) n).toLinearMap
    have hdim : Module.finrank K S = Module.finrank K T :=
      LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
        (splitRows (K := K) n).toLinearMap (splitRows (K := K) n).injective S)
    rw [tuple_split_card]
    change (pairedSet left right (tupleColumn left right) T).card ≤ _
    calc
      _ ≤ (priorSet (tupleColumn left right) T).card * P ^ Module.finrank K (vertical T) :=
        pair_step_count left right (tupleColumn left right) P hinj hE hprojection T
      _ ≤ P ^ Module.finrank K (prefixSpace T) * P ^ Module.finrank K (vertical T) :=
        Nat.mul_le_mul_right _ (ih (prefixSpace T))
      _ = P ^ Module.finrank K S := by
        rw [← pow_add, rank_increment, ← hdim]
end ThreeSum.TernaryCoverTupleCount
