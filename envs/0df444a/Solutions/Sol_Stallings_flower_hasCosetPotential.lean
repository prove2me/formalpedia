-- Prove2me | solution 1 for Stallings.flower_hasCosetPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:14:08.402712+00:00
-- url     : https://prove2.me/submissions/aab4cdbc-0eb5-450a-aa94-2f6edad15337

import Definitions.Def_Stallings_Folding
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Definitions.Def_Stallings_Flower
import Theorems.Thm_Stallings_CosetEquivalent_refl
import Theorems.Thm_Stallings_CosetEquivalent_right_mul
import Theorems.Thm_Stallings_CosetEquivalent_symm
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff


section
namespace Stallings
private theorem flowerPos_internal (S : List Word) (i : Fin S.length) {k : Nat}
    (hk0 : 0 < k) (hk : k < (S.get i).length) :
    flowerPos S i k (Nat.le_of_lt hk) = some (i, ⟨k, by
      have hmax := length_le_maxWordLength_of_mem (List.get_mem S i)
      omega⟩) := by
  unfold flowerPos
  rw [dif_neg (by omega : ¬ k = 0), dif_neg (by omega : ¬ k = (S.get i).length)]
private theorem flowerPotential_pos (S : List Word) (i : Fin S.length) {k : Nat}
    (hk : k < (S.get i).length) :
    flowerPotential S (flowerPos S i k (Nat.le_of_lt hk)) =
      wordEval ((S.get i).take k) := by
  by_cases hk0 : k = 0
  · subst k
    simp [flowerPos, flowerPotential, wordEval_nil]
  · have hpos := flowerPos_internal S i (Nat.pos_of_ne_zero hk0) hk
    rw [hpos]
    change (if k < (S.get i).length then wordEval ((S.get i).take k) else 1) = _
    rw [if_pos hk]
private theorem wordEval_take_succ (w : Word) (k : Nat) (hk : k < w.length) :
    wordEval (w.take (k + 1)) = wordEval (w.take k) * letterEval (w.get ⟨k, hk⟩) := by
  rw [← List.take_concat_get' w k hk, wordEval_append]
  simp
private theorem flowerForwardPotential (S : List Word) (i : Fin S.length)
    (j : Fin (S.get i).length) :
    CosetEquivalent (generatorSubgroup S)
      (flowerPotential S (flowerTarget S i j))
      (flowerPotential S (flowerSource S i j) * letterEval (flowerLabel S i j)) := by
  let w := S.get i
  let k := j.val
  have hk : k < w.length := j.isLt
  have hsource : flowerPotential S (flowerSource S i j) = wordEval (w.take k) := by
    simpa [flowerSource, w, k] using flowerPotential_pos S i hk
  have hstep : wordEval (w.take (k + 1)) =
      wordEval (w.take k) * letterEval (flowerLabel S i j) := by
    simpa [w, k, flowerLabel] using wordEval_take_succ w k hk
  have hkNext : k + 1 ≤ w.length := Nat.succ_le_of_lt hk
  by_cases hinternal : k + 1 < w.length
  · have htarget : flowerPotential S (flowerTarget S i j) = wordEval (w.take (k + 1)) := by
      simpa [flowerTarget, w, k] using flowerPotential_pos S i hinternal
    have hval : flowerPotential S (flowerTarget S i j) =
        flowerPotential S (flowerSource S i j) * letterEval (flowerLabel S i j) := by
      rw [htarget, hsource, ← hstep]
    rw [hval]
    exact CosetEquivalent.refl _ _
  · have hterminal : k + 1 = w.length := by omega
    have htarget : flowerPotential S (flowerTarget S i j) = 1 := by
      change flowerPotential S (flowerPos S i (k + 1) hkNext) = 1
      unfold flowerPos
      rw [dif_neg (by omega : ¬ k + 1 = 0), dif_pos hterminal]
      simp [flowerPotential]
    have htake : w.take (k + 1) = w := by
      apply List.take_of_length_le
      omega
    have hgen : wordEval w ∈ generatorSubgroup S :=
      Subgroup.subset_closure ⟨i, rfl⟩
    have hcoset : CosetEquivalent (generatorSubgroup S) 1 (wordEval w) := by
      change (wordEval w)⁻¹ ∈ generatorSubgroup S
      exact (generatorSubgroup S).inv_mem hgen
    rw [htarget, hsource, ← hstep, htake]
    simpa using hcoset
end Stallings
end

set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution (S : List Word) :
    HasCosetPotential (flowerGraph S) (generatorSubgroup S) (flowerPotential S) := by
  intro v x w hedge
  change w ∈ (Finset.univ.filter (flowerEdge S v x)) at hedge
  have hedg := (Finset.mem_filter.mp hedge).2
  rcases hedg with ⟨i, j, hforward | hbackward⟩
  · rcases hforward with ⟨rfl, rfl, rfl⟩
    exact flowerForwardPotential S i j
  · rcases hbackward with ⟨rfl, rfl, rfl⟩
    have hf := flowerForwardPotential S i j
    have hr := CosetEquivalent.right_mul hf (letterEval (letterInv (flowerLabel S i j)))
    simpa [letterEval_inv, mul_assoc] using CosetEquivalent.symm hr
end Stallings
