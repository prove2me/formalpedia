-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.card_constantTorus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:33:04.709792+00:00
-- url     : https://prove2.me/submissions/2699fc94-2d50-4908-9375-5d18883159d6

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.Coset.Card
import Lean.Elab.Tactic.Omega
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K)
    [Fintype F] (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Nat.card (constantTorus f epsilon y) = Fintype.card F + 1 := by
  classical
  letI : Fact (∀ r : F, r ^ 2 ≠ epsilon + 0 * r) :=
    ⟨fun r => by simpa using hNonSquare r⟩
  letI : Fintype (QuadraticAlgebra F epsilon 0) :=
    Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd epsilon 0).symm
  have hQuadraticCard : Nat.card (QuadraticAlgebra F epsilon 0) =
      Fintype.card F * Fintype.card F := by
    rw [Nat.card_congr (QuadraticAlgebra.equivProd epsilon 0), Nat.card_prod,
      Nat.card_eq_fintype_card]
  have hKernelCard : Nat.card (constantProjectiveMap f epsilon y).ker =
      Fintype.card F - 1 := by
    rw [Nat.card_congr (constantKernelEquiv f epsilon y hOne hTwo),
      Nat.card_units, Nat.card_eq_fintype_card]
  have hProduct := (constantProjectiveMap f epsilon y).ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_units, hQuadraticCard, hKernelCard,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (constantProjectiveMap f epsilon y)).toEquiv] at hProduct
  have hFieldCard : 1 < Fintype.card F := Fintype.one_lt_card
  have hFactor : Fintype.card F * Fintype.card F - 1 =
      (Fintype.card F + 1) * (Fintype.card F - 1) := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (Fintype.card_pos (α := F)))
    rw [hq]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    have hIdentity : (q + 1) * (q + 1) = (q + 1 + 1) * q + 1 := by ring
    omega
  change Nat.card (constantProjectiveMap f epsilon y).range = _
  exact Nat.eq_of_mul_eq_mul_right (by omega)
    (hProduct.symm.trans hFactor)
end QEC.Coding.ExpanderCodes.QuaternionGenerators
