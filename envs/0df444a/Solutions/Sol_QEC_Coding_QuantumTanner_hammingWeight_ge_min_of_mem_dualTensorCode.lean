-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.hammingWeight_ge_min_of_mem_dualTensorCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:24:01.418696+00:00
-- url     : https://prove2.me/submissions/d1b404b2-d4a0-4dbe-a46d-83b95d5df5b9

import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Theorems.Thm_QEC_Coding_QuantumTanner_columnContraction_mem_of_mem_dualTensorCode
import Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_columnContraction_le
import Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_columnRestriction_le
import Theorems.Thm_QEC_Coding_LinearCode_dual_dual_carrier_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution [DecidableEq F]
    (CA : LinearCode F A) (CB : LinearCode F B) (dA dB : Nat)
    (hA : ∀ a : Word F A, a ∈ CA.carrier → a ≠ 0 → dA ≤ HammingWeight a)
    (hB : ∀ b : Word F B, b ∈ CB.carrier → b ≠ 0 → dB ≤ HammingWeight b)
    (x : Word F (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier) (hne : x ≠ 0) :
    min dA dB ≤ HammingWeight x := by
  by_contra hsmall
  have hlt : HammingWeight x < min dA dB := Nat.lt_of_not_ge hsmall
  have hltA : HammingWeight x < dA := lt_of_lt_of_le hlt (min_le_left _ _)
  have hltB : HammingWeight x < dB := lt_of_lt_of_le hlt (min_le_right _ _)
  have hcolumns : ∀ b, columnRestriction b x ∈ CA.carrier := by
    intro b
    rw [← LinearCode.dual_dual_carrier_eq CA]
    refine (CA.dual.mem_dual _).2 ?_
    intro a ha
    have hcontract : columnContraction a x = 0 := by
      by_contra hc
      have hbound := hB _ (columnContraction_mem_of_mem_dualTensorCode CA CB a ha x hx) hc
      have hweight := hammingWeight_columnContraction_le a x
      omega
    have hb := congrFun hcontract b
    change wordPairing a (columnRestriction b x) = 0 at hb
    rw [wordPairing_apply, dotProduct_comm]
    exact hb
  have hxzero : x = 0 := by
    ext ab
    have hcolumn : columnRestriction ab.2 x = 0 := by
      by_contra hc
      have hbound := hA _ (hcolumns ab.2) hc
      have hweight := hammingWeight_columnRestriction_le ab.2 x
      omega
    exact congrFun hcolumn ab.1
  exact hne hxzero
end QEC.Coding.QuantumTanner
