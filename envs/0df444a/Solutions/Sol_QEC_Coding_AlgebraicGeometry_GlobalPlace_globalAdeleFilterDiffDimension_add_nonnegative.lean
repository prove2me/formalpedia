-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterDiffDimension_add_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:52:00.726652+00:00
-- url     : https://prove2.me/submissions/9e5a204c-5356-472f-8345-21c8c5f65a5e

import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdelePlaceIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleEffectiveIncrement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilterDiffDimension_mono_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilterDiffDimension_add_placeDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
namespace GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
attribute [local instance] globalAdeleFilterAddCommGroup
attribute [local instance] globalAdeleFilterModule
private theorem globalAdeleFilterDiffDimension_add_placeDivisor_of_le
    {D M : Divisor (GlobalPlace k F)} (P : GlobalPlace k F) (hDM : D ≤ M) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D (M + placeDivisor P) =
      globalAdeleFilterDiffDimension (k := k) (F := F) D M +
        residueDegree (k := k) (F := F) P := by
  have hMN : M ≤ M + placeDivisor P := by
    intro Q
    simp only [Finsupp.add_apply]
    exact le_add_of_nonneg_right (by
      by_cases hQP : Q = P
      · subst Q
        simp
      · rw [placeDivisor_apply_of_ne P Q (Ne.symm hQP)])
  rw [globalAdeleFilterDiffDimension_mono_add hDM hMN,
    globalAdeleFilterDiffDimension_add_placeDivisor]
private theorem globalAdeleFilterDiffDimension_add_single_nat
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) (n : ℕ) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D
        (D + Finsupp.single P (n : ℤ)) =
      n * residueDegree (k := k) (F := F) P := by
  classical
  induction n with
  | zero =>
      simp only [Nat.cast_zero, Finsupp.single_zero, add_zero, zero_mul]
      rw [globalAdeleFilterDiffDimension]
      have hp : Submodule.comap
          (globalAdeleFilter (k := k) (F := F) D).subtype
          (globalAdeleFilter (k := k) (F := F) D) = ⊤ := by
        ext a
        simp
      rw [hp]
      exact Module.finrank_zero_of_subsingleton
  | succ n ih =>
      let M := D + Finsupp.single P (n : ℤ)
      have hDM : D ≤ M := by
        intro Q
        dsimp only [M]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      have heq : D + Finsupp.single P ((n + 1 : ℕ) : ℤ) =
          M + placeDivisor P := by
        dsimp only [M]
        ext Q
        simp only [Finsupp.add_apply, Finsupp.single_apply, placeDivisor]
        split <;> omega
      calc
        globalAdeleFilterDiffDimension (k := k) (F := F) D
            (D + Finsupp.single P ((n + 1 : ℕ) : ℤ)) =
            globalAdeleFilterDiffDimension (k := k) (F := F) D
              (M + placeDivisor P) := by rw [heq]
        _ = globalAdeleFilterDiffDimension (k := k) (F := F) D M +
            residueDegree (k := k) (F := F) P :=
          globalAdeleFilterDiffDimension_add_placeDivisor_of_le P hDM
        _ = n * residueDegree (k := k) (F := F) P +
            residueDegree (k := k) (F := F) P := by
          rw [← ih]
        _ = (n + 1) * residueDegree (k := k) (F := F) P := by ring
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterAddCommGroup
attribute [local instance] globalAdeleFilterAddCommGroup
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterModule
attribute [local instance] globalAdeleFilterModule
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (D E : Divisor (GlobalPlace k F)) (hE : Divisor.Nonnegative E) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D (D + E) =
      (Divisor.degree (residueDegree (k := k) (F := F)) E).toNat := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero =>
      rw [add_zero, globalAdeleFilterDiffDimension, Divisor.degree_zero]
      have hp : Submodule.comap
          (globalAdeleFilter (k := k) (F := F) D).subtype
          (globalAdeleFilter (k := k) (F := F) D) = ⊤ := by
        ext a
        simp
      rw [hp]
      exact Module.finrank_zero_of_subsingleton
  | single_add P coefficient tail hPtail hcoefficient ih =>
      have htailP : tail P = 0 := Finsupp.notMem_support_iff.mp hPtail
      have htail : Divisor.Nonnegative tail := by
        intro Q
        by_cases hQP : Q = P
        · subst Q
          rw [htailP]
        · have hQE := hE Q
          simpa [Finsupp.single_apply, hQP] using hQE
      have hcoefficient_nonnegative : 0 ≤ coefficient := by
        have hPE := hE P
        simpa [Finsupp.single_apply, htailP] using hPE
      let M := D + tail
      let N := M + Finsupp.single P (coefficient.toNat : ℤ)
      have hDM : D ≤ M := by
        intro Q
        dsimp only [M]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (htail Q)
      have hMN : M ≤ N := by
        intro Q
        dsimp only [N]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      have hfirst := ih D htail
      have hsecond : globalAdeleFilterDiffDimension (k := k) (F := F) M N =
          coefficient.toNat * residueDegree (k := k) (F := F) P := by
        exact globalAdeleFilterDiffDimension_add_single_nat M P coefficient.toNat
      have hdegree_tail : 0 ≤
          Divisor.degree (residueDegree (k := k) (F := F)) tail :=
        Divisor.degree_nonnegative _ tail htail
      have hdegree_total : 0 ≤
          Divisor.degree (residueDegree (k := k) (F := F))
            (Finsupp.single P coefficient + tail) :=
        Divisor.degree_nonnegative _ _ hE
      have hdegree :
          Divisor.degree (residueDegree (k := k) (F := F))
              (Finsupp.single P coefficient + tail) =
            coefficient * (residueDegree (k := k) (F := F) P : ℤ) +
              Divisor.degree (residueDegree (k := k) (F := F)) tail := by
        rw [Divisor.degree_add]
        simp [Divisor.degree, Divisor.degreeHom]
      have hdegree_nat :
          (Divisor.degree (residueDegree (k := k) (F := F))
              (Finsupp.single P coefficient + tail)).toNat =
            coefficient.toNat * residueDegree (k := k) (F := F) P +
              (Divisor.degree (residueDegree (k := k) (F := F)) tail).toNat := by
        have htail_cast :
            ((Divisor.degree (residueDegree (k := k) (F := F)) tail).toNat : ℤ) =
              Divisor.degree (residueDegree (k := k) (F := F)) tail :=
          Int.toNat_of_nonneg hdegree_tail
        have htotal_cast :
            ((Divisor.degree (residueDegree (k := k) (F := F))
              (Finsupp.single P coefficient + tail)).toNat : ℤ) =
                Divisor.degree (residueDegree (k := k) (F := F))
                  (Finsupp.single P coefficient + tail) :=
          Int.toNat_of_nonneg hdegree_total
        apply Int.ofNat_injective
        change ((Divisor.degree (residueDegree (k := k) (F := F))
            (Finsupp.single P coefficient + tail)).toNat : ℤ) =
          ((coefficient.toNat * residueDegree (k := k) (F := F) P +
            (Divisor.degree (residueDegree (k := k) (F := F)) tail).toNat : ℕ) : ℤ)
        rw [htotal_cast, Nat.cast_add, Nat.cast_mul,
          Int.toNat_of_nonneg hcoefficient_nonnegative, htail_cast]
        exact hdegree
      have htotal : globalAdeleFilterDiffDimension (k := k) (F := F) D N =
          (Divisor.degree (residueDegree (k := k) (F := F))
            (Finsupp.single P coefficient + tail)).toNat := by
        have hadd := globalAdeleFilterDiffDimension_mono_add hDM hMN
        rw [hadd, hfirst, hsecond, hdegree_nat, Nat.add_comm]
      have heq : D + (Finsupp.single P coefficient + tail) = N := by
        dsimp only [N, M]
        rw [Int.toNat_of_nonneg hcoefficient_nonnegative]
        abel
      rw [heq]
      exact htotal
end QEC.Coding.AlgebraicGeometry.GlobalPlace
