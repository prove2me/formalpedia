-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.cubicPairing_combinedWord_eq_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:45:15.495619+00:00
-- url     : https://prove2.me/submissions/2eebbe7a-ea1f-405c-8bf6-a9a1db89541a

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_row_eq_sumElim
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cubicPairing_combinedWord
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] primeQuditRegisterLabelFintype
namespace CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site]
private theorem logicalTripleContribution_eq_diagonal (R : CubicRowFamily p Logical Stabilizer Site)
    (q : Logical → ZMod p) (a : Logical) :
    ∑ b : Logical, ∑ c : Logical,
      q a * q b * q c * cubicPairing p (R.logicalRow a) (R.logicalRow b) (R.logicalRow c) =
      q a ^ 3 * R.epsilon a := by
  classical
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single a]
    · simp only [epsilon]
      ring
    · intro c _ hca
      rw [R.logicalTriple_offDiagonal_zero a a c]
      · simp
      · intro hall
        exact hca hall.2.symm
    · simp
  · intro b _ hba
    apply Finset.sum_eq_zero
    intro c _
    rw [R.logicalTriple_offDiagonal_zero a b c]
    · simp
    · intro hall
      exact hba hall.1.symm
  · simp
end CubicRowFamily
namespace CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site] [DecidableEq Site]
end CubicRowFamily
namespace CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site] [DecidableEq Site]
end CubicRowFamily
namespace fiveSiteSingleLogical
end fiveSiteSingleLogical
end QEC.Distillation.KT19PrimeQuditCSS
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] primeQuditRegisterLabelFintype
open QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site]
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_633
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_634
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_635
namespace QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
theorem _root_.solution (R : CubicRowFamily p Logical Stabilizer Site)
    (q : Logical ⊕ Stabilizer → ZMod p) :
    cubicPairing p (R.combinedWord q) (R.combinedWord q) (R.combinedWord q) =
      ∑ a : Logical, q (Sum.inl a) ^ 3 * R.epsilon a := by
  rw [R.cubicPairing_combinedWord]
  have houter :
      (∑ s : Stabilizer, ∑ b : Logical ⊕ Stabilizer, ∑ c : Logical ⊕ Stabilizer,
        q (Sum.inr s) * q b * q c *
          cubicPairing p (R.row (Sum.inr s)) (R.row b) (R.row c)) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro c _
    have hzero : cubicPairing p (R.row (Sum.inr s)) (R.row b) (R.row c) = 0 := by
      rw [R.row_eq_sumElim]
      exact R.stabilizerTriple_zero (Sum.inr s) b c (Or.inl ⟨s, rfl⟩)
    rw [hzero]
    simp
  rw [Fintype.sum_sum_type, houter, add_zero]
  apply Finset.sum_congr rfl
  intro a _
  have hsecond :
      (∑ s : Stabilizer, ∑ c : Logical ⊕ Stabilizer,
        q (Sum.inl a) * q (Sum.inr s) * q c *
          cubicPairing p (R.row (Sum.inl a)) (R.row (Sum.inr s)) (R.row c)) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro c _
    have hzero : cubicPairing p (R.row (Sum.inl a)) (R.row (Sum.inr s)) (R.row c) = 0 := by
      rw [R.row_eq_sumElim]
      exact R.stabilizerTriple_zero (Sum.inl a) (Sum.inr s) c (Or.inr (Or.inl ⟨s, rfl⟩))
    rw [hzero]
    simp
  rw [Fintype.sum_sum_type, hsecond, add_zero]
  calc
    (∑ b : Logical, ∑ c : Logical ⊕ Stabilizer,
      q (Sum.inl a) * q (Sum.inl b) * q c *
        cubicPairing p (R.row (Sum.inl a)) (R.row (Sum.inl b)) (R.row c)) =
      ∑ b : Logical, ∑ c : Logical,
        q (Sum.inl a) * q (Sum.inl b) * q (Sum.inl c) *
          cubicPairing p (R.row (Sum.inl a)) (R.row (Sum.inl b)) (R.row (Sum.inl c)) := by
      apply Finset.sum_congr rfl
      intro b _
      have hthird :
          (∑ s : Stabilizer,
            q (Sum.inl a) * q (Sum.inl b) * q (Sum.inr s) *
              cubicPairing p (R.row (Sum.inl a)) (R.row (Sum.inl b)) (R.row (Sum.inr s))) = 0 := by
        apply Finset.sum_eq_zero
        intro s _
        have hzero : cubicPairing p (R.row (Sum.inl a)) (R.row (Sum.inl b))
            (R.row (Sum.inr s)) = 0 := by
          simpa [row] using R.stabilizerTriple_zero (Sum.inl a) (Sum.inl b) (Sum.inr s)
            (Or.inr (Or.inr ⟨s, rfl⟩))
        rw [hzero]
        simp
      rw [Fintype.sum_sum_type, hthird, add_zero]
    _ = q (Sum.inl a) ^ 3 * R.epsilon a := by
      simpa [row] using
        R.logicalTripleContribution_eq_diagonal (fun a => q (Sum.inl a)) a
end QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
