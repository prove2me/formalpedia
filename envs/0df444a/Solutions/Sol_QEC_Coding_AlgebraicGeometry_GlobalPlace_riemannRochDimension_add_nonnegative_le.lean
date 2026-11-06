-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_add_nonnegative_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:54:36.381202+00:00
-- url     : https://prove2.me/submissions/34dd7a8e-b9e7-4a74-b326-ed9b0c01c527

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveIncrement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_add_placeDivisor_le
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
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] riemannRochEffectiveIncrementAlgebra
attribute [local instance] riemannRochEffectiveIncrementScalarTower
namespace GlobalPlace
attribute [local instance] finiteDimensionalRiemannRochSubmodule
private theorem riemannRochDimension_add_placeDivisor_le'
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    riemannRochDimension (G + placeDivisor P) ≤
      riemannRochDimension G + residueDegree (k := k) (F := F) P := by
  exact riemannRochDimension_add_placeDivisor_le G P
private theorem riemannRochDimension_add_single_nat_le
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) (n : ℕ) :
    riemannRochDimension (D + Finsupp.single P (n : ℤ)) ≤
      riemannRochDimension D +
        n * residueDegree (k := k) (F := F) P := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      let M := D + Finsupp.single P (n : ℤ)
      have heq : D + Finsupp.single P ((n + 1 : ℕ) : ℤ) =
          M + placeDivisor P := by
        dsimp only [M]
        ext Q
        simp only [Finsupp.add_apply, Finsupp.single_apply, placeDivisor]
        split <;> omega
      calc
        riemannRochDimension
            (D + Finsupp.single P ((n + 1 : ℕ) : ℤ)) =
            riemannRochDimension (M + placeDivisor P) := by rw [heq]
        _ ≤ riemannRochDimension M +
            residueDegree (k := k) (F := F) P :=
          riemannRochDimension_add_placeDivisor_le'
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F M P
        _ ≤ (riemannRochDimension D +
              n * residueDegree (k := k) (F := F) P) +
            residueDegree (k := k) (F := F) P :=
          Nat.add_le_add_right ih _
        _ = riemannRochDimension D +
            (n + 1) * residueDegree (k := k) (F := F) P := by
          rw [Nat.add_mul, one_mul, add_assoc]
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochEffectiveIncrementAlgebra
attribute [local instance] riemannRochEffectiveIncrementAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochEffectiveIncrementScalarTower
attribute [local instance] riemannRochEffectiveIncrementScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.finiteDimensionalRiemannRochSubmodule
attribute [local instance] finiteDimensionalRiemannRochSubmodule
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (D E : Divisor (GlobalPlace k F)) (hE : Divisor.Nonnegative E) :
    riemannRochDimension (D + E) ≤
      riemannRochDimension D +
        (Divisor.degree (residueDegree (k := k) (F := F)) E).toNat := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero =>
      simp
  | single_add P coefficient tail hPtail hcoefficient ih =>
      have htailP : tail P = 0 := Finsupp.notMem_support_iff.mp hPtail
      have htail : Divisor.Nonnegative tail := by
        intro Q
        by_cases hQP : Q = P
        · subst Q
          rw [htailP]
        · simpa [Finsupp.single_apply, hQP] using hE Q
      have hcoefficient_nonnegative : 0 ≤ coefficient := by
        simpa [Finsupp.single_apply, htailP] using hE P
      let M := D + tail
      let N := M + Finsupp.single P (coefficient.toNat : ℤ)
      have hfirst := ih D htail
      have hsecond : riemannRochDimension N ≤
          riemannRochDimension M +
            coefficient.toNat * residueDegree (k := k) (F := F) P := by
        exact riemannRochDimension_add_single_nat_le
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F M P coefficient.toNat
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
      have htotal : riemannRochDimension N ≤
          riemannRochDimension D +
            (Divisor.degree (residueDegree (k := k) (F := F))
              (Finsupp.single P coefficient + tail)).toNat := by
        calc
          riemannRochDimension N ≤
              riemannRochDimension M +
                coefficient.toNat * residueDegree (k := k) (F := F) P := hsecond
          _ ≤ (riemannRochDimension D +
                (Divisor.degree (residueDegree (k := k) (F := F)) tail).toNat) +
              coefficient.toNat * residueDegree (k := k) (F := F) P :=
            Nat.add_le_add_right hfirst _
          _ = riemannRochDimension D +
              (Divisor.degree (residueDegree (k := k) (F := F))
                (Finsupp.single P coefficient + tail)).toNat := by
            rw [hdegree_nat]
            ac_rfl
      have heq : D + (Finsupp.single P coefficient + tail) = N := by
        dsimp only [N, M]
        rw [Int.toNat_of_nonneg hcoefficient_nonnegative]
        abel
      rw [heq]
      exact htotal
end QEC.Coding.AlgebraicGeometry.GlobalPlace
