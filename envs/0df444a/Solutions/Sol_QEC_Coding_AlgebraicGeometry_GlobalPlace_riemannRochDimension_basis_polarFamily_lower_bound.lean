-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_basis_polarFamily_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:03:54.246867+00:00
-- url     : https://prove2.me/submissions/79c30932-1940-4c4b-abc4-04c59b745f65

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveDimensionBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_polarDivisor_of_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_chartVariable_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mul_mem_riemannRochSubmodule_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_zero_mem_riemannRochSubmodule
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
private theorem pow_mem_riemannRochSubmodule_nsmul_polar
    {x : F} (hx : x ≠ 0) (n : ℕ) :
    x ^ n ∈ riemannRochSubmodule
      (n • polarDivisor (k := k) (F := F) x) := by
  induction n with
  | zero =>
      simp only [pow_zero, zero_nsmul]
      rw [mem_riemannRochSubmodule_iff]
      intro P
      simp
  | succ n ih =>
      have hxmem := mem_riemannRochSubmodule_polarDivisor_of_ne_zero
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hx
      have hmul := mul_mem_riemannRochSubmodule_add ih hxmem
      simpa [pow_succ, succ_nsmul] using hmul
omit ρ τ φ s in
private theorem nsmul_polarDivisor_mono {D : Divisor (GlobalPlace k F)}
    (hD : Divisor.Nonnegative D) {j r : ℕ} (hjr : j ≤ r) :
    j • D ≤ r • D := by
  intro P
  change (j : ℤ) * D P ≤ (r : ℤ) * D P
  exact mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hjr) (hD P)
private theorem polarDivisor_le_basisPoleBound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → F) (i : ι) :
    polarDivisor (k := k) (F := F) (b i) ≤
      basisPoleBound (k := k) (F := F) b := by
  classical
  simp only [basisPoleBound]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ => polarDivisor_nonnegative
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F (b j))
private theorem basis_mem_riemannRochSubmodule_basisPoleBound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → F) (i : ι) :
    b i ∈ riemannRochSubmodule (basisPoleBound (k := k) (F := F) b) := by
  by_cases hi : b i = 0
  · rw [hi]
    exact zero_mem_riemannRochSubmodule _
  · exact riemannRochSubmodule_mono
      (polarDivisor_le_basisPoleBound
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F b i)
      (mem_riemannRochSubmodule_polarDivisor_of_ne_zero
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hi)
private theorem basis_mul_pow_mem_polarFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → F) {x : F} (hx : x ≠ 0) (r : ℕ)
    (i : ι) (j : ℕ) (hj : j ≤ r) :
    b i * x ^ j ∈ riemannRochSubmodule
      (basisPoleBound (k := k) (F := F) b +
        r • polarDivisor (k := k) (F := F) x) := by
  apply mul_mem_riemannRochSubmodule_add
    (basis_mem_riemannRochSubmodule_basisPoleBound
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F b i)
  exact riemannRochSubmodule_mono
    (nsmul_polarDivisor_mono (k := k) (F := F)
      (polarDivisor_nonnegative
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F x) hj)
    (pow_mem_riemannRochSubmodule_nsmul_polar
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hx j)
omit [Finite k] in
private theorem linearIndependent_fin_pow_of_transcendental
    {L : Type*} [Field L] [Algebra k L] {x : L}
    (hx : Transcendental k x) (r : ℕ) :
    LinearIndependent k fun j : Fin (r + 1) => x ^ (j : ℕ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  let p : Polynomial k :=
    ∑ i : Fin (r + 1), Polynomial.C (g i) * Polynomial.X ^ (i : ℕ)
  have hzero : Polynomial.aeval x p = 0 := by
    have hsum : Polynomial.aeval x p =
        ∑ i : Fin (r + 1), g i • x ^ (i : ℕ) := by
      simp only [p, map_sum, map_mul, Polynomial.aeval_C]
      congr 1
      ext i
      rw [Polynomial.aeval_X_pow, Algebra.smul_def, mul_comm]
    rw [hsum, hg]
  have hp0 : p = 0 := (transcendental_iff.mp hx) p hzero
  have hcoeff : g j = 0 := by
    have hgj : g j = p.coeff (j : ℕ) := by
      classical
      dsimp only [p]
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
      · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
      · intro i _ hne
        rw [Polynomial.coeff_C_mul_X_pow]
        split_ifs with h
        · exact absurd h (Fin.val_ne_of_ne hne.symm)
        · rfl
      · simp
    rw [hgj, hp0, Polynomial.coeff_zero]
  exact hcoeff
private theorem linearIndependent_basis_mul_chartVariable_pow {n r : ℕ}
    (b : Module.Basis (Fin n) (RatFunc k) F) :
    LinearIndependent k fun p : Fin n × Fin (r + 1) =>
      (b p.1 : F) * chartVariable (k := k) (F := F) ^ (p.2 : ℕ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let c : Fin n → RatFunc k := fun i =>
    ∑ j : Fin (r + 1), g (i, j) • RatFunc.X ^ (j : ℕ)
  have hsingle : ∀ i, algebraMap (RatFunc k) F (c i) * (b i : F) =
      ∑ j : Fin (r + 1), g (i, j) •
        ((b i : F) * chartVariable (k := k) (F := F) ^ (j : ℕ)) := by
    intro i
    dsimp only [c, chartVariable]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [Algebra.smul_def, map_mul, map_pow, mul_assoc,
      mul_comm (b i : F), IsScalarTower.algebraMap_apply k (RatFunc k) F]
  have hcombo : ∑ i : Fin n, algebraMap (RatFunc k) F (c i) * (b i : F) = 0 := by
    rw [Finset.sum_congr rfl fun i _ => hsingle i, ← Finset.sum_product']
    exact hg
  have hcombo' : ∑ i : Fin n, c i • (b i : F) = 0 := by
    simpa only [Algebra.smul_def] using hcombo
  have hc : ∀ i, c i = 0 :=
    (Fintype.linearIndependent_iff.mp b.linearIndependent) c hcombo'
  intro p
  have hc' := hc p.1
  have hlin := linearIndependent_fin_pow_of_transcendental
    (k := k) (L := RatFunc k) RatFunc.transcendental_X r
  rw [Fintype.linearIndependent_iff] at hlin
  exact hlin (fun j => g (p.1, j)) (by dsimp only [c] at hc'; exact hc') p.2
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
theorem _root_.solution {n r : ℕ}
    (b : Module.Basis (Fin n) (RatFunc k) F) :
    n * (r + 1) ≤ riemannRochDimension
      (basisPoleBound (k := k) (F := F) b +
        r • polarDivisor (k := k) (F := F)
          (chartVariable (k := k) (F := F))) := by
  let C := basisPoleBound (k := k) (F := F) b
  let B := polarDivisor (k := k) (F := F)
    (chartVariable (k := k) (F := F))
  let x := chartVariable (k := k) (F := F)
  let v : Fin n × Fin (r + 1) → F := fun p =>
    (b p.1 : F) * x ^ (p.2 : ℕ)
  have hmem : ∀ p, v p ∈ riemannRochSubmodule (C + r • B) := by
    intro p
    exact basis_mul_pow_mem_polarFamily
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F b
      (chartVariable_ne_zero
        (ρ := ρ) k F)
      r p.1 (p.2 : ℕ) (Nat.le_of_lt_succ p.2.isLt)
  have hlin : LinearIndependent k v :=
    linearIndependent_basis_mul_chartVariable_pow
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F b
  have hspan : span k (Set.range v) ≤ riemannRochSubmodule (C + r • B) := by
    refine span_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact hmem p
  have hcard : n * (r + 1) ≤ Module.finrank k (span k (Set.range v)) := by
    have heq := finrank_span_eq_card hlin
    simp [heq, Fintype.card_prod, Fintype.card_fin]
  have hle : Module.finrank k (span k (Set.range v)) ≤
      Module.finrank k (riemannRochSubmodule (C + r • B)) :=
    Submodule.finrank_mono hspan
  exact hcard.trans (by
    simpa only [riemannRochDimension, C, B] using hle)
end QEC.Coding.AlgebraicGeometry.GlobalPlace
