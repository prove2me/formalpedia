-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldFinrank_le_polarDivisor_chartVariable_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:30:27.067583+00:00
-- url     : https://prove2.me/submissions/49898e2c-94c8-47ef-875d-16a056c28628

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveDimensionBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_basisPoleBound_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_chartVariable_transcendental
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_chartVariable_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_basis_polarFamily_lower_bound
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_le_degree_add_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
section
namespace QEC.Coding.AlgebraicGeometry
open Polynomial Submodule
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] riemannRochPolarFamilyAlgebra
attribute [local instance] riemannRochPolarFamilyPolynomialScalarTower
attribute [local instance] riemannRochPolarFamilyRationalScalarTower
namespace GlobalPlace
attribute [local instance] riemannRochPolarFamilyFiniteDimensional
private theorem exists_valuation_gt_one_of_not_isAlgebraic
    {x : F} (hx : ¬IsAlgebraic k x) :
    ∃ P : GlobalPlace k F, 1 < P.valuation x := by
  by_contra h
  push Not at h
  exact hx (isAlgebraic_of_valuation_le_one
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F x h)
private theorem residueDegree_pos (P : GlobalPlace k F) :
    0 < residueDegree (k := k) (F := F) P := by
  letI : Algebra k (residueField P) := residueAlgebra P
  letI : FiniteDimensional k (residueField P) :=
    residueField_finiteDimensional P
  rw [residueDegree_eq_finrank P]
  exact Module.finrank_pos
private theorem divisorDegree_mono
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    Divisor.degree (residueDegree (k := k) (F := F)) D ≤
      Divisor.degree (residueDegree (k := k) (F := F)) E := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hdegree_nonnegative : 0 ≤
      Divisor.degree (residueDegree (k := k) (F := F)) (E - D) :=
    Divisor.degree_nonnegative _ _ hnonnegative
  have heq : D + (E - D) = E := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [← heq, Divisor.degree_add]
  exact le_add_of_nonneg_right hdegree_nonnegative
private theorem polarDivisor_degree_pos
    {x : F} (hx0 : x ≠ 0) (hx : ¬IsAlgebraic k x) :
    0 < Divisor.degree (residueDegree (k := k) (F := F))
      (polarDivisor (k := k) (F := F) x) := by
  classical
  obtain ⟨P, hP⟩ := exists_valuation_gt_one_of_not_isAlgebraic
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hx
  have hcoefficient : 0 < polarDivisor (k := k) (F := F) x P := by
    have hlog : WithZero.log 1 < WithZero.log (P.valuation x) :=
      (WithZero.log_lt_log one_ne_zero
        ((P.valuation).ne_zero_iff.mpr hx0)).2 hP
    simp only [WithZero.log_one] at hlog
    simp only [polarDivisor, dif_neg hx0, Finsupp.sup_apply]
    change 0 < max
      (-(principalDivisor (k := k) (F := F) (Units.mk0 x hx0) P)) 0
    rw [principalDivisor_apply]
    simp only [Units.val_mk0]
    have hnegOrder : 0 < -P.order x := by
      simpa only [order, neg_neg] using hlog
    exact hnegOrder.trans_le (le_max_left _ _)
  have hsingle : Finsupp.single P
      (polarDivisor (k := k) (F := F) x P) ≤
      polarDivisor (k := k) (F := F) x := by
    intro Q
    by_cases hQP : Q = P
    · subst Q
      simp
    · rw [Finsupp.single_apply, if_neg (Ne.symm hQP)]
      exact polarDivisor_nonnegative
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F x Q
  have hle := divisorDegree_mono
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hsingle
  have hsingleDegree :
      Divisor.degree (residueDegree (k := k) (F := F))
        (Finsupp.single P (polarDivisor (k := k) (F := F) x P)) =
      polarDivisor (k := k) (F := F) x P *
        (residueDegree (k := k) (F := F) P : ℤ) := by
    simp [Divisor.degree, Divisor.degreeHom]
  rw [hsingleDegree] at hle
  have hresidue : 0 < (residueDegree (k := k) (F := F) P : ℤ) := by
    exact_mod_cast residueDegree_pos
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F P
  exact (mul_pos hcoefficient hresidue).trans_le hle
private theorem le_of_forall_nat_mul_le {n d c : ℕ} (_hd : 0 < d)
    (h : ∀ r : ℕ, n * (r + 1) ≤ d * r + c) : n ≤ d := by
  by_contra hn
  have hdn : d < n := lt_of_not_ge hn
  have hnd : 0 < n - d := Nat.sub_pos_of_lt hdn
  have hbound : ∀ r : ℕ, (n - d) * r + n ≤ c := by
    intro r
    have hr := h r
    have hn_eq : d + (n - d) = n := by omega
    rw [Nat.mul_succ, ← hn_eq, add_mul] at hr
    omega
  let q := (c - n) / (n - d)
  have hq_lt : c - n < (q + 1) * (n - d) := by
    have hmod := Nat.mod_lt (c - n) hnd
    calc
      c - n = (n - d) * q + (c - n) % (n - d) :=
        (Nat.div_add_mod (c - n) (n - d)).symm
      _ = q * (n - d) + (c - n) % (n - d) := by rw [Nat.mul_comm]
      _ < q * (n - d) + (n - d) := by gcongr
      _ = (q + 1) * (n - d) := by ring
  have hq := hbound (q + 1)
  have : (n - d) * (q + 1) ≤ c - n := by omega
  rw [Nat.mul_comm] at this
  exact (not_lt_of_ge this) hq_lt
private theorem divisorDegree_nsmul
    (n : ℕ) (D : Divisor (GlobalPlace k F)) :
    Divisor.degree (residueDegree (k := k) (F := F)) (n • D) =
      (n : ℤ) * Divisor.degree (residueDegree (k := k) (F := F)) D := by
  simpa only [Divisor.degree, nsmul_eq_mul] using
    (Divisor.degreeHom (residueDegree (k := k) (F := F))).map_nsmul n D
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Polynomial Submodule
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarFamilyAlgebra
attribute [local instance] riemannRochPolarFamilyAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarFamilyPolynomialScalarTower
attribute [local instance] riemannRochPolarFamilyPolynomialScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarFamilyRationalScalarTower
attribute [local instance] riemannRochPolarFamilyRationalScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochPolarFamilyFiniteDimensional
attribute [local instance] riemannRochPolarFamilyFiniteDimensional
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    [IsFullConstantField k F] :
    Module.finrank (RatFunc k) F ≤
      (Divisor.degree (residueDegree (k := k) (F := F))
        (polarDivisor (k := k) (F := F)
          (chartVariable (k := k) (F := F)))).toNat := by
  let n := Module.finrank (RatFunc k) F
  let b : Module.Basis (Fin n) (RatFunc k) F := Module.finBasis (RatFunc k) F
  let C := basisPoleBound (k := k) (F := F) b
  let B := polarDivisor (k := k) (F := F)
    (chartVariable (k := k) (F := F))
  have hBnonnegative : Divisor.Nonnegative B :=
    polarDivisor_nonnegative
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F _
  have hCnonnegative : Divisor.Nonnegative C :=
    basisPoleBound_nonnegative
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F b
  have hBdegree_nonnegative : 0 ≤
      Divisor.degree (residueDegree (k := k) (F := F)) B :=
    Divisor.degree_nonnegative _ _ hBnonnegative
  have hBdegree_pos : 0 <
      Divisor.degree (residueDegree (k := k) (F := F)) B :=
    polarDivisor_degree_pos
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
      (chartVariable_ne_zero
        (ρ := ρ) k F)
      (chartVariable_transcendental
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
  have hdpos : 0 <
      (Divisor.degree (residueDegree (k := k) (F := F)) B).toNat := by
    rw [← Int.toNat_of_nonneg hBdegree_nonnegative] at hBdegree_pos
    exact Int.ofNat_lt.mp hBdegree_pos
  apply le_of_forall_nat_mul_le hdpos
  intro r
  let D := C + r • B
  have hDnonnegative : Divisor.Nonnegative D := by
    intro P
    exact add_nonneg (hCnonnegative P)
      (mul_nonneg (Int.natCast_nonneg r) (hBnonnegative P))
  have hlower : n * (r + 1) ≤ riemannRochDimension D :=
    riemannRochDimension_basis_polarFamily_lower_bound
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F b
  have hupper : riemannRochDimension D ≤
      (Divisor.degree (residueDegree (k := k) (F := F)) D).toNat + 1 :=
    riemannRochDimension_le_degree_add_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D hDnonnegative
  have hCdegree_nonnegative : 0 ≤
      Divisor.degree (residueDegree (k := k) (F := F)) C :=
    Divisor.degree_nonnegative _ _ hCnonnegative
  have hdegree :
      Divisor.degree (residueDegree (k := k) (F := F)) D =
        Divisor.degree (residueDegree (k := k) (F := F)) C +
          (r : ℤ) * Divisor.degree (residueDegree (k := k) (F := F)) B := by
    dsimp only [D]
    rw [Divisor.degree_add, divisorDegree_nsmul
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
  have hdegree_nat :
      (Divisor.degree (residueDegree (k := k) (F := F)) D).toNat =
        (Divisor.degree (residueDegree (k := k) (F := F)) C).toNat +
          r * (Divisor.degree (residueDegree (k := k) (F := F)) B).toNat := by
    have hDdegree_nonnegative : 0 ≤
        Divisor.degree (residueDegree (k := k) (F := F)) D :=
      Divisor.degree_nonnegative _ _ hDnonnegative
    apply Int.ofNat_injective
    change ((Divisor.degree (residueDegree (k := k) (F := F)) D).toNat : ℤ) =
      ((Divisor.degree (residueDegree (k := k) (F := F)) C).toNat : ℤ) +
        (r : ℤ) *
          ((Divisor.degree (residueDegree (k := k) (F := F)) B).toNat : ℤ)
    rw [Int.toNat_of_nonneg hDdegree_nonnegative,
      Int.toNat_of_nonneg hCdegree_nonnegative,
      Int.toNat_of_nonneg hBdegree_nonnegative]
    exact hdegree
  calc
    n * (r + 1) ≤ riemannRochDimension D := hlower
    _ ≤ (Divisor.degree (residueDegree (k := k) (F := F)) D).toNat + 1 := hupper
    _ = (Divisor.degree (residueDegree (k := k) (F := F)) B).toNat * r +
        ((Divisor.degree (residueDegree (k := k) (F := F)) C).toNat + 1) := by
      rw [hdegree_nat]
      ring
end QEC.Coding.AlgebraicGeometry.GlobalPlace
