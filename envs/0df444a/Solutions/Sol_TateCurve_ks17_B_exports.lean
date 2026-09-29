-- Prove2me | solution 1 for TateCurve.ks17_B_exports
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d5efc800-00e8-5baf-a95f-10d9d4f58e9a

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_DefectLines
import Definitions.Def_NumberTheory_DivisorConvolution
import Definitions.Def_TateCurve_KeystoneVocab

import Theorems.Thm_TateCurve_ks17_A_exports
import Theorems.Thm_TateCurve_pointX_inv
import Theorems.Thm_TateCurve_pointX_q_mul
import Theorems.Thm_TateCurve_pointX_zpow_mul
import Theorems.Thm_TateCurve_defectCoeff_one
import Theorems.Thm_TateCurve_pointX_qExpansion
import Theorems.Thm_TateCurve_pointY_qExpansion
import Theorems.Thm_TateCurve_pointY_q_mul
import Theorems.Thm_TateCurve_pointY_inv
import Theorems.Thm_TateCurve_pointY_zpow_mul
import Theorems.Thm_TateCurve_exists_zpow_mul_mem_annulus
import Theorems.Thm_TateCurve_equation_pointX_pointY_of_defectCoeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_ks17_B_exports

open scoped NNReal
p2m_open "TateCurve P2MW.S_TateCurve_ks17_B_exports.TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset"

universe u_1 u_2

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt cauchyMul_eq_boundary_add_int cauchyMul_cube_eq_boundary_add_int xCoeffFull_of_pos cauchyMulInt_xx_eq_sum_Sols defectCoeff_eq_boundary_add_int Fz Gz Fz_zero Gz_zero Fz_neg Gz_neg Fz_natCast Gz_natCast Fz_mul_Fz Fz_mul_Gz xDivTerm_eq_mul_Fz tent xfun_mul_Fz_eq_tent tent_eq_sq_add_sum_Ico cauchyMul cauchyMul_zero xCoeffFull xCoeffFull_zero a₄Coeff a₄Coeff_zero a₆Coeff xfun yfun pointX pointY term b a₄ curve xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff psifun svComplex LatticeRep OnHalfLattice ks17_A_exports"
p2m_open "TateCurve"

theorem psiCoeffFull_zero : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K},
      psiCoeffFull u 0 = 2 * yfun u + xfun u :=
  TateCurve.ks17_A_exports.{u_1}.1

theorem psiCoeffFull_succ_eq_divisorSum : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (N : ℕ),
      psiCoeffFull u (N + 1) = ∑ d ∈ (N + 1).divisors, (d : K) ^ 2 * (u ^ d - u⁻¹ ^ d) :=
  TateCurve.ks17_A_exports.{u_1}.2.1

theorem coeff_eq_of_hasSum_eq : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {A Bc : ℕ → K} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ q' : K, q' ≠ 0 → ‖q'‖ < ε → ∃ S : K,
      HasSum (fun N => A N * q' ^ N) S ∧ HasSum (fun N => Bc N * q' ^ N) S),
      ∀ N, A N = Bc N :=
  TateCurve.ks17_A_exports.{u_1}.2.2.1

theorem addDefectDiff_q_mul_left : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} (hq0 : q ≠ 0),
      addDefectDiff q (q * u) v = addDefectDiff q u v :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.1

theorem expansionRegion_of_spectator : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q' w v : K} (hq'0 : q' ≠ 0)
    (hlo : ‖q'‖ < ‖w‖) (hhi : ‖q'‖ * ‖w‖ < 1) (hwne : ‖w‖ ≠ 1)
    (hv : ‖v‖ = 1) (hv1 : v ≠ 1),
      ExpansionRegion q' w v :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.1

theorem rowExpansion_of_coeff_eq : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (hrow : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      addDefectSumCoeff u' v' M
        = ∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)),
      ∀ q' u' v' : K, ExpansionRegion q' u' v' → HasSum (fun M : ℕ => (∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)) * q' ^ M) (addDefectSum q' u' v') :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.1

theorem diffExpansion_of_coeff_eq : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {f : K → K → ℕ → K}
    (hcoeff : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      f u' v' M = addDefectDiffCoeff u' v' M),
      ∀ q' u' v' : K, ExpansionRegion q' u' v' → HasSum (fun M : ℕ => f u' v' M * q' ^ M) (addDefectDiff q' u' v') :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.1

theorem addDefectDiffCoeff_zero : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1),
      addDefectDiffCoeff u v 0 = 0 :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.1

theorem sub_negY_curve : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (q x y : K),
      y - (curve q).toAffine.negY x y = 2 * y + x :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.1

theorem symAdd_sum_of_region_of_not_halfLattice : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hreg : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hp : AddParams q u v) (hloc : ¬ (OnHalfLattice q u ∧ OnHalfLattice q v)),
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = symSumNum q (pointX q u) (pointX q v) :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.2.1

theorem diff_identity_of_region_of_not_halfLattice : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hreg : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v) (hloc : ¬ (OnHalfLattice q u ∧ OnHalfLattice q v)),
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.1

theorem not_onHalfLattice_of_norm_eq_one : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q w : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hw : ‖w‖ = 1),
      ¬ OnHalfLattice q w :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.1

theorem addDefectSum_qExpansion : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} (hreg : ExpansionRegion q u v),
      HasSum (fun N : ℕ => addDefectSumCoeff u v N * q ^ N) (addDefectSum q u v) :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem addDefectSumCoeff_zero : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1),
      addDefectSumCoeff u v 0 = 0 :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem addDefectDiff_eq_zero_iff' : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K},
      addDefectDiff q u v = 0 ↔ (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem addDefectDiff_eq_zero_iff_curve : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K},
      addDefectDiff q u v = 0 ↔ (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((pointY q u - (curve q).toAffine.negY (pointX q u) (pointY q u)) * (pointY q v - (curve q).toAffine.negY (pointX q v) (pointY q v))) :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

namespace AddParams p2m_export "TateCurve.AddParams" "swap" end AddParams
p2m_open_scoped "TateCurve.AddParams" in
theorem AddParams.latticeRep : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} {u' v' : K} (hp : AddParams q u v)
    (hu' : LatticeRep q u u') (hv' : LatticeRep q v v'),
      AddParams q u' v' :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt cauchyMul_eq_boundary_add_int cauchyMul_cube_eq_boundary_add_int xCoeffFull_of_pos cauchyMulInt_xx_eq_sum_Sols defectCoeff_eq_boundary_add_int Fz Gz Fz_zero Gz_zero Fz_neg Gz_neg Fz_natCast Gz_natCast Fz_mul_Fz Fz_mul_Gz xDivTerm_eq_mul_Fz tent xfun_mul_Fz_eq_tent tent_eq_sq_add_sum_Ico cauchyMul cauchyMul_zero xCoeffFull xCoeffFull_zero a₄Coeff a₄Coeff_zero a₆Coeff xfun yfun pointX pointY term b a₄ curve xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff psifun svComplex LatticeRep OnHalfLattice ks17_A_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] {u v w : K}

section ParamSymm

theorem Fz_inv (a : ℤ) : Fz v⁻¹ a = Fz v a := by
  simp only [Fz, inv_zpow, ← zpow_neg, neg_neg]
  ring

theorem Gz_inv (a : ℤ) : Gz v⁻¹ a = -Gz v a := by
  simp only [Gz, inv_zpow, ← zpow_neg, neg_neg]
  ring

end ParamSymm

section CrossLaws

theorem Fz_mul_add_Fz_mul_inv (hu : u ≠ 0) (hv : v ≠ 0) (a : ℤ) :
    Fz (u * v) a + Fz (u * v⁻¹) a = Fz u a * Fz v a + 2 * Fz u a + 2 * Fz v a := by
  have hua : u ^ a ≠ 0 := zpow_ne_zero a hu
  have hva : v ^ a ≠ 0 := zpow_ne_zero a hv
  simp only [Fz, zpow_neg, mul_zpow, inv_zpow, mul_inv, inv_inv]
  field_simp
  ring

theorem Fz_mul_sub_Fz_mul_inv (hu : u ≠ 0) (hv : v ≠ 0) (a : ℤ) :
    Fz (u * v) a - Fz (u * v⁻¹) a = Gz u a * Gz v a := by
  have hua : u ^ a ≠ 0 := zpow_ne_zero a hu
  have hva : v ^ a ≠ 0 := zpow_ne_zero a hv
  simp only [Fz, Gz, zpow_neg, mul_zpow, inv_zpow, mul_inv, inv_inv]
  field_simp
  ring

theorem xCoeff_mul_add_xCoeff_mul_inv (hu : u ≠ 0) (hv : v ≠ 0) (n : ℕ) :
    xCoeff (u * v) n + xCoeff (u * v⁻¹) n
      = ∑ d ∈ n.divisors,
          (d : K) * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ)) := by
  rw [xCoeff, xCoeff, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz, ← mul_add, Fz_mul_add_Fz_mul_inv hu hv]

end CrossLaws

section DiffFactor

theorem Fz_sub_Fz_factor_mul (hu : u ≠ 0) (hv : v ≠ 0) (d : ℕ) :
    Fz u (d : ℤ) - Fz v (d : ℤ) = (u ^ d - v ^ d) * (1 - ((u * v) ^ d)⁻¹) := by
  have hud : u ^ d ≠ 0 := pow_ne_zero d hu
  have hvd : v ^ d ≠ 0 := pow_ne_zero d hv
  rw [Fz_natCast, Fz_natCast]
  simp only [inv_pow, mul_pow, mul_inv]
  field_simp
  ring

theorem Fz_sub_Fz_factor_div (hu : u ≠ 0) (hv : v ≠ 0) (d : ℕ) :
    Fz u (d : ℤ) - Fz v (d : ℤ) = (u ^ d - (v ^ d)⁻¹) * (1 - ((u * v⁻¹) ^ d)⁻¹) := by
  have hud : u ^ d ≠ 0 := pow_ne_zero d hu
  have hvd : v ^ d ≠ 0 := pow_ne_zero d hv
  rw [Fz_natCast, Fz_natCast]
  simp only [inv_pow, mul_pow, mul_inv, inv_inv]
  field_simp
  ring

theorem xfun_sub_xfun_mul_clear (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (xfun u - xfun v) * ((1 - u) ^ 2 * (1 - v) ^ 2) = (u - v) * (1 - u * v) := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have h1v : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  rw [xfun, xfun]
  field_simp
  ring

end DiffFactor

section CrossAbsorption

theorem xfun_mul_one_sub_pow_inv_mul_one_sub_pow_inv (hw0 : w ≠ 0) (hw1 : w ≠ 1) (a b : ℕ) :
    xfun w * ((1 - (w ^ a)⁻¹) * (1 - (w ^ b)⁻¹))
      = w * (∑ i ∈ Finset.range a, w ^ i) * (∑ i ∈ Finset.range b, w ^ i)
          * (w ^ a)⁻¹ * (w ^ b)⁻¹ := by
  have h1w : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hwa : w ^ a ≠ 0 := pow_ne_zero a hw0
  have hwb : w ^ b ≠ 0 := pow_ne_zero b hw0
  have ea : (1 : K) - (w ^ a)⁻¹ = (∑ i ∈ Finset.range a, w ^ i) * (w - 1) * (w ^ a)⁻¹ := by
    rw [geom_sum_mul]
    field_simp
  have eb : (1 : K) - (w ^ b)⁻¹ = (∑ i ∈ Finset.range b, w ^ i) * (w - 1) * (w ^ b)⁻¹ := by
    rw [geom_sum_mul]
    field_simp
  rw [ea, eb, xfun]
  field_simp
  ring

theorem xfun_mul_mul_Fz_sub_mul_Fz_sub (hu : u ≠ 0) (hv : v ≠ 0) (huv1 : u * v ≠ 1)
    (a b : ℕ) :
    xfun (u * v) * ((Fz u (a : ℤ) - Fz v (a : ℤ)) * (Fz u (b : ℤ) - Fz v (b : ℤ)))
      = (u ^ a - v ^ a) * (u ^ b - v ^ b)
          * (u * v * (∑ i ∈ Finset.range a, (u * v) ^ i) * (∑ i ∈ Finset.range b, (u * v) ^ i)
              * ((u * v) ^ a)⁻¹ * ((u * v) ^ b)⁻¹) := by
  have habs := xfun_mul_one_sub_pow_inv_mul_one_sub_pow_inv (w := u * v)
    (mul_ne_zero hu hv) huv1 a b
  rw [Fz_sub_Fz_factor_mul hu hv a, Fz_sub_Fz_factor_mul hu hv b]
  linear_combination (u ^ a - v ^ a) * (u ^ b - v ^ b) * habs

theorem xfun_mul_inv_mul_Fz_sub_mul_Fz_sub (hu : u ≠ 0) (hv : v ≠ 0) (huv1 : u * v⁻¹ ≠ 1)
    (a b : ℕ) :
    xfun (u * v⁻¹) * ((Fz u (a : ℤ) - Fz v (a : ℤ)) * (Fz u (b : ℤ) - Fz v (b : ℤ)))
      = (u ^ a - (v ^ a)⁻¹) * (u ^ b - (v ^ b)⁻¹)
          * (u * v⁻¹ * (∑ i ∈ Finset.range a, (u * v⁻¹) ^ i)
              * (∑ i ∈ Finset.range b, (u * v⁻¹) ^ i)
              * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ b)⁻¹) := by
  have h := xfun_mul_mul_Fz_sub_mul_Fz_sub (v := v⁻¹) hu (inv_ne_zero hv) huv1 a b
  simpa [Fz_inv, inv_pow] using h

end CrossAbsorption

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt cauchyMul_eq_boundary_add_int cauchyMul_cube_eq_boundary_add_int xCoeffFull_of_pos cauchyMulInt_xx_eq_sum_Sols defectCoeff_eq_boundary_add_int Fz Gz Fz_zero Gz_zero Fz_neg Gz_neg Fz_natCast Gz_natCast Fz_mul_Fz Fz_mul_Gz xDivTerm_eq_mul_Fz tent xfun_mul_Fz_eq_tent tent_eq_sq_add_sum_Ico cauchyMul cauchyMul_zero xCoeffFull xCoeffFull_zero a₄Coeff a₄Coeff_zero a₆Coeff xfun yfun pointX pointY term b a₄ curve xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff psifun svComplex LatticeRep OnHalfLattice ks17_A_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] {u v w : K}

section BoundaryDiff

theorem xfun_sub_xfun_eq (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    xfun u - xfun v = -((Fz u 1 - Fz v 1) * (xfun u * xfun v)) := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have h1v : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  simp only [xfun, Fz, zpow_neg, zpow_one]
  field_simp
  ring

theorem xCoeff_sub_xCoeff_divisorSum (u v : K) (M : ℕ) :
    xCoeff u M - xCoeff v M
      = ∑ d ∈ M.divisors, (d : K) * (Fz u (d : ℤ) - Fz v (d : ℤ)) := by
  rw [xCoeff, xCoeff, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz]
  ring

end BoundaryDiff

section MixedCrossAbsorption

theorem xfun_mul_mul_xfun_sub_mul_Fz_sub (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huv1 : u * v ≠ 1) (d : ℕ) :
    xfun (u * v) * ((xfun u - xfun v) * (Fz u (d : ℤ) - Fz v (d : ℤ)))
      = -((u - v) * (u ^ d - v ^ d) * (∑ i ∈ Finset.range d, (u * v) ^ i)
          * ((u * v) ^ d)⁻¹ * (xfun u * xfun v)) := by
  have huv0 : u * v ≠ 0 := mul_ne_zero hu0 hv0
  have hcancel : u * v * (u * v)⁻¹ = 1 := mul_inv_cancel₀ huv0
  have hbase := xfun_mul_mul_Fz_sub_mul_Fz_sub hu0 hv0 huv1 1 d
  simp only [pow_one, Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_one,
    mul_one] at hbase
  rw [xfun_sub_xfun_eq hu0 hv0 hu1 hv1]
  linear_combination (-(xfun u * xfun v)) * hbase
    - ((u - v) * (u ^ d - v ^ d) * (∑ i ∈ Finset.range d, (u * v) ^ i) * ((u * v) ^ d)⁻¹
        * (xfun u * xfun v)) * hcancel

theorem xfun_mul_inv_mul_xfun_sub_mul_Fz_sub (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huv1 : u * v⁻¹ ≠ 1) (d : ℕ) :
    xfun (u * v⁻¹) * ((xfun u - xfun v) * (Fz u (d : ℤ) - Fz v (d : ℤ)))
      = -((u - v⁻¹) * (u ^ d - (v ^ d)⁻¹) * (∑ i ∈ Finset.range d, (u * v⁻¹) ^ i)
          * ((u * v⁻¹) ^ d)⁻¹ * (xfun u * xfun v)) := by
  have huv0 : u * v⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hv0)
  have hcancel : u * v⁻¹ * (u * v⁻¹)⁻¹ = 1 := mul_inv_cancel₀ huv0
  have hbase := xfun_mul_inv_mul_Fz_sub_mul_Fz_sub hu0 hv0 huv1 1 d
  simp only [pow_one, Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_one,
    mul_one] at hbase
  rw [xfun_sub_xfun_eq hu0 hv0 hu1 hv1]
  linear_combination (-(xfun u * xfun v)) * hbase
    - ((u - v⁻¹) * (u ^ d - (v ^ d)⁻¹) * (∑ i ∈ Finset.range d, (u * v⁻¹) ^ i)
        * ((u * v⁻¹) ^ d)⁻¹ * (xfun u * xfun v)) * hcancel

theorem xfun_add_mul_xfun_sub_mul_Fz_sub (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (d : ℕ) :
    (xfun (u * v) + xfun (u * v⁻¹)) * ((xfun u - xfun v) * (Fz u (d : ℤ) - Fz v (d : ℤ)))
      = -(((u - v) * (u ^ d - v ^ d) * (∑ i ∈ Finset.range d, (u * v) ^ i)
            * ((u * v) ^ d)⁻¹
          + (u - v⁻¹) * (u ^ d - (v ^ d)⁻¹) * (∑ i ∈ Finset.range d, (u * v⁻¹) ^ i)
              * ((u * v⁻¹) ^ d)⁻¹)
          * (xfun u * xfun v)) := by
  have h1 := xfun_mul_mul_xfun_sub_mul_Fz_sub hu0 hv0 hu1 hv1 huvm d
  have h2 := xfun_mul_inv_mul_xfun_sub_mul_Fz_sub hu0 hv0 hu1 hv1 huvd d
  linear_combination h1 + h2

theorem xfun_add_mul_xfun_sub_mul_xCoeff_sub (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (M : ℕ) :
    (xfun (u * v) + xfun (u * v⁻¹)) * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M))
      = ∑ d ∈ M.divisors, (d : K) *
          (-(((u - v) * (u ^ d - v ^ d) * (∑ i ∈ Finset.range d, (u * v) ^ i)
                * ((u * v) ^ d)⁻¹
              + (u - v⁻¹) * (u ^ d - (v ^ d)⁻¹) * (∑ i ∈ Finset.range d, (u * v⁻¹) ^ i)
                  * ((u * v⁻¹) ^ d)⁻¹)
            * (xfun u * xfun v))) := by
  rw [xCoeff_sub_xCoeff_divisorSum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  linear_combination (d : K) * xfun_add_mul_xfun_sub_mul_Fz_sub hu0 hv0 hu1 hv1 huvm huvd d

end MixedCrossAbsorption

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt cauchyMul_eq_boundary_add_int cauchyMul_cube_eq_boundary_add_int xCoeffFull_of_pos cauchyMulInt_xx_eq_sum_Sols defectCoeff_eq_boundary_add_int Fz Gz Fz_zero Gz_zero Fz_neg Gz_neg Fz_natCast Gz_natCast Fz_mul_Fz Fz_mul_Gz xDivTerm_eq_mul_Fz tent xfun_mul_Fz_eq_tent tent_eq_sq_add_sum_Ico cauchyMul cauchyMul_zero xCoeffFull xCoeffFull_zero a₄Coeff a₄Coeff_zero a₆Coeff xfun yfun pointX pointY term b a₄ curve xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff psifun svComplex LatticeRep OnHalfLattice ks17_A_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section CauchyAlgebra

theorem cauchyMul_comm (c d : ℕ → K) (N : ℕ) : cauchyMul c d N = cauchyMul d c N := by
  rw [cauchyMul, cauchyMul,
    ← Finset.Nat.sum_antidiagonal_swap (f := fun p : ℕ × ℕ => d p.1 * c p.2)]
  exact Finset.sum_congr rfl fun p _ => by simp [mul_comm]

theorem cauchyMul_sub_sub (P Q : ℕ → K) (b : ℕ) :
    cauchyMul (fun i => P i - Q i) (fun i => P i - Q i) b
      = cauchyMul P P b - 2 * cauchyMul P Q b + cauchyMul Q Q b := by
  have hswap : cauchyMul Q P b = cauchyMul P Q b := cauchyMul_comm Q P b
  simp only [cauchyMul] at hswap ⊢
  have hpoint : (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal b, (P kl.1 - Q kl.1) * (P kl.2 - Q kl.2))
      = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal b,
          (P kl.1 * P kl.2 - P kl.1 * Q kl.2 - Q kl.1 * P kl.2 + Q kl.1 * Q kl.2) :=
    Finset.sum_congr rfl fun kl _ => by ring
  rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hswap]
  ring

theorem cauchyMul_cross_collect (c P Q : ℕ → K) (N : ℕ) :
    cauchyMul c (cauchyMul (fun i => P i - Q i) (fun i => P i - Q i)) N
      = cauchyMul c (cauchyMul P P) N - 2 * cauchyMul c (cauchyMul P Q) N
        + cauchyMul c (cauchyMul Q Q) N := by
  have hsq : ∀ b, cauchyMul (fun i => P i - Q i) (fun i => P i - Q i) b
      = cauchyMul P P b - 2 * cauchyMul P Q b + cauchyMul Q Q b := cauchyMul_sub_sub P Q
  rw [cauchyMul_eq_sum_range c (cauchyMul P P), cauchyMul_eq_sum_range c (cauchyMul P Q),
    cauchyMul_eq_sum_range c (cauchyMul Q Q), cauchyMul_eq_sum_range c]
  have hpoint : (∑ i ∈ Finset.range (N + 1),
        c i * cauchyMul (fun j => P j - Q j) (fun j => P j - Q j) (N - i))
      = ∑ i ∈ Finset.range (N + 1),
          (c i * cauchyMul P P (N - i) - 2 * (c i * cauchyMul P Q (N - i))
            + c i * cauchyMul Q Q (N - i)) :=
    Finset.sum_congr rfl fun i _ => by rw [hsq]; ring
  rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem cauchyMul_eq_head_add_sum_Icc (c d : ℕ → K) (N : ℕ) :
    cauchyMul c d N = c 0 * d N + ∑ a ∈ Finset.Icc 1 N, c a * d (N - a) := by
  have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  rw [cauchyMul_eq_sum_range, hset, Finset.sum_insert h0, Nat.sub_zero]

end CauchyAlgebra

section TripleSplit
@[scoped simp] theorem cauchyMulIntTriple_zero (c d e : ℕ → K) : cauchyMulIntTriple c d e 0 = 0 := by
  simp [cauchyMulIntTriple]

theorem cauchyMul_triple_eq_boundary_add_int (c d e : ℕ → K) {N : ℕ} (hN : 0 < N) :
    cauchyMul c (cauchyMul d e) N
      = c 0 * d 0 * e N + c 0 * e 0 * d N + d 0 * e 0 * c N
        + c 0 * cauchyMulInt d e N + d 0 * cauchyMulInt c e N + e 0 * cauchyMulInt c d N
        + cauchyMulIntTriple c d e N := by
  have hterm : ∀ i ∈ Finset.Ico 1 N,
      c i * cauchyMul d e (N - i)
        = d 0 * (c i * e (N - i)) + e 0 * (c i * d (N - i))
          + c i * cauchyMulInt d e (N - i) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [cauchyMul_eq_boundary_add_int d e (show 0 < N - i by omega)]
    ring
  have hsplit : cauchyMulInt c (cauchyMul d e) N
      = d 0 * cauchyMulInt c e N + e 0 * cauchyMulInt c d N + cauchyMulIntTriple c d e N := by
    rw [cauchyMulInt, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, cauchyMulInt, cauchyMulInt,
      cauchyMulIntTriple]
  rw [cauchyMul_eq_boundary_add_int c (cauchyMul d e) hN, hsplit,
    cauchyMul_eq_boundary_add_int d e hN, cauchyMul_zero]
  ring

end TripleSplit

section Grouping

theorem addDefectSumCoeff_eq_grouped (u v : K) {M : ℕ} (hM : 0 < M) :
    addDefectSumCoeff u v M
      = (xfun (u * v) + xfun (u * v⁻¹))
            * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                (fun i => xCoeffFull u i - xCoeffFull v i) M
        + 2 * ((xfun (u * v) + xfun (u * v⁻¹))
            * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M)))
        + (∑ a ∈ Finset.Icc 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
            * cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
                (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))
        - 2 * cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull u) (xCoeffFull v)) M
        - 2 * cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull v) (xCoeffFull v)) M
        - cauchyMul (xCoeffFull u) (xCoeffFull v) M
        - 2 * cauchyMul a₄Coeff (xCoeffFull u) M
        - 2 * cauchyMul a₄Coeff (xCoeffFull v) M
        - 4 * a₆Coeff M := by

  have hcollM := cauchyMul_cross_collect (xCoeffFull (u * v)) (xCoeffFull u) (xCoeffFull v) M
  have hcollD := cauchyMul_cross_collect (xCoeffFull (u * v⁻¹)) (xCoeffFull u) (xCoeffFull v) M

  have hheadM := cauchyMul_eq_head_add_sum_Icc (xCoeffFull (u * v))
    (cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
      (fun i => xCoeffFull u i - xCoeffFull v i)) M
  have hheadD := cauchyMul_eq_head_add_sum_Icc (xCoeffFull (u * v⁻¹))
    (cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
      (fun i => xCoeffFull u i - xCoeffFull v i)) M
  rw [xCoeffFull_zero] at hheadM
  rw [xCoeffFull_zero] at hheadD

  have hinner : cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
      (fun i => xCoeffFull u i - xCoeffFull v i) M
      = (xfun u - xfun v) * (xCoeff u M - xCoeff v M)
        + (xCoeff u M - xCoeff v M) * (xfun u - xfun v)
        + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
            (fun i => xCoeffFull u i - xCoeffFull v i) M := by
    have h := cauchyMul_eq_boundary_add_int (fun i => xCoeffFull u i - xCoeffFull v i)
      (fun i => xCoeffFull u i - xCoeffFull v i) hM
    simpa only [xCoeffFull_zero, xCoeffFull_of_pos u hM, xCoeffFull_of_pos v hM] using h

  have hmerge : (∑ a ∈ Finset.Icc 1 M, xCoeffFull (u * v) a
        * cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
            (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))
      + ∑ a ∈ Finset.Icc 1 M, xCoeffFull (u * v⁻¹) a
          * cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
              (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)
      = ∑ a ∈ Finset.Icc 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
          * cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
              (fun i => xCoeffFull u i - xCoeffFull v i) (M - a) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_Icc] at ha
    rw [xCoeffFull_of_pos (u * v) (show 0 < a by omega),
      xCoeffFull_of_pos (u * v⁻¹) (show 0 < a by omega)]
    ring
  simp only [addDefectSumCoeff]
  linear_combination (-1 : K) * hcollM - hcollD + hheadM + hheadD
    + (xfun (u * v) + xfun (u * v⁻¹)) * hinner + hmerge

end Grouping

section FullSplit

theorem addDefectSumCoeff_eq_boundary_add_int (u v : K) {M : ℕ} (hM : 0 < M) :
    addDefectSumCoeff u v M
      = ((xfun (u * v) + xfun (u * v⁻¹))
            * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                (fun i => xCoeffFull u i - xCoeffFull v i) M
          + 2 * ((xfun (u * v) + xfun (u * v⁻¹))
              * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M)))
          + (xCoeff (u * v) M + xCoeff (u * v⁻¹) M) * (xfun u - xfun v) ^ 2
          + ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
              * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a)))
                  + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                      (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)))
        - (2 * (xfun u ^ 2 * xCoeff v M) + 4 * (xfun u * xfun v * xCoeff u M)
            + 4 * (xfun u * cauchyMulInt (xCoeffFull u) (xCoeffFull v) M)
            + 2 * (xfun v * cauchyMulInt (xCoeffFull u) (xCoeffFull u) M)
            + 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M)
        - (4 * (xfun u * xfun v * xCoeff v M)
            + 2 * (xfun u * cauchyMulInt (xCoeffFull v) (xCoeffFull v) M)
            + 2 * (xfun v ^ 2 * xCoeff u M)
            + 4 * (xfun v * cauchyMulInt (xCoeffFull u) (xCoeffFull v) M)
            + 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M)
        - (xfun u * xCoeff v M + xfun v * xCoeff u M
            + cauchyMulInt (xCoeffFull u) (xCoeffFull v) M)
        - (2 * (a₄Coeff M * xfun u) + 2 * cauchyMulInt a₄Coeff (xCoeffFull u) M)
        - (2 * (a₄Coeff M * xfun v) + 2 * cauchyMulInt a₄Coeff (xCoeffFull v) M)
        - 4 * a₆Coeff M := by

  have hcross : (∑ a ∈ Finset.Icc 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
        * cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
            (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))
      = (xCoeff (u * v) M + xCoeff (u * v⁻¹) M) * (xfun u - xfun v) ^ 2
        + ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
            * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a)))
                + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                    (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)) := by
    have htop : cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
        (fun i => xCoeffFull u i - xCoeffFull v i) (M - M) = (xfun u - xfun v) ^ 2 := by
      rw [Nat.sub_self, cauchyMul_zero]
      simp only [xCoeffFull_zero]
      ring
    have hsummand : ∀ a ∈ Finset.Ico 1 M,
        (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
            * cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
                (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)
          = (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
              * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a)))
                  + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                      (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)) := by
      intro a ha
      rw [Finset.mem_Ico] at ha
      have hMa : 0 < M - a := by omega
      rw [cauchyMul_eq_boundary_add_int _ _ hMa]
      simp only [xCoeffFull_zero, xCoeffFull_of_pos u hMa, xCoeffFull_of_pos v hMa]
      ring
    have hset : Finset.Icc 1 M = insert M (Finset.Ico 1 M) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
      omega
    have hMnot : M ∉ Finset.Ico 1 M := by simp
    rw [hset, Finset.sum_insert hMnot, htop, Finset.sum_congr rfl hsummand]

  have htri1 := cauchyMul_triple_eq_boundary_add_int (xCoeffFull u) (xCoeffFull u)
    (xCoeffFull v) hM
  have htri2 := cauchyMul_triple_eq_boundary_add_int (xCoeffFull u) (xCoeffFull v)
    (xCoeffFull v) hM
  have hPQ := cauchyMul_eq_boundary_add_int (xCoeffFull u) (xCoeffFull v) hM
  have hA4P := cauchyMul_eq_boundary_add_int a₄Coeff (xCoeffFull u) hM
  have hA4Q := cauchyMul_eq_boundary_add_int a₄Coeff (xCoeffFull v) hM
  simp only [xCoeffFull_zero, xCoeffFull_of_pos u hM, xCoeffFull_of_pos v hM, a₄Coeff_zero,
    zero_mul, zero_add] at htri1 htri2 hPQ hA4P hA4Q
  rw [addDefectSumCoeff_eq_grouped u v hM, hcross]
  linear_combination (-2 : K) * htri1 - 2 * htri2 - hPQ - 2 * hA4P - 2 * hA4Q

end FullSplit

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

open scoped NNReal

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt cauchyMul_eq_boundary_add_int cauchyMul_cube_eq_boundary_add_int xCoeffFull_of_pos cauchyMulInt_xx_eq_sum_Sols defectCoeff_eq_boundary_add_int Fz Gz Fz_zero Gz_zero Fz_neg Gz_neg Fz_natCast Gz_natCast Fz_mul_Fz Fz_mul_Gz xDivTerm_eq_mul_Fz tent xfun_mul_Fz_eq_tent tent_eq_sq_add_sum_Ico cauchyMul cauchyMul_zero xCoeffFull xCoeffFull_zero a₄Coeff a₄Coeff_zero a₆Coeff xfun yfun pointX pointY term b a₄ curve xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff psifun svComplex LatticeRep OnHalfLattice ks17_A_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate

section Engine

variable {β : Type*} [AddCommMonoid β]

theorem sum_psiAdd (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → β) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1),
        F (x.1, x.2.1 - x.2.2.2, x.1 + x.2.2.1, x.2.2.2)
      = ∑ y ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), F y := by
  refine Finset.sum_nbij' (i := fun x => (x.1, x.2.1 - x.2.2.2, x.1 + x.2.2.1, x.2.2.2))
    (j := fun y => (y.1, y.2.1 + y.2.2.2, y.2.2.1 - y.1, y.2.2.2)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxS, hlt⟩ := Finset.mem_filter.1 hx
    obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hxS
    replace hlt : x.2.2.2 < x.2.1 := hlt
    have e1 : x.1 * (x.2.1 - x.2.2.2) + x.1 * x.2.2.2 = x.1 * x.2.1 := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have e2 : (x.1 + x.2.2.1) * x.2.2.2 = x.1 * x.2.2.2 + x.2.2.1 * x.2.2.2 :=
      Nat.add_mul _ _ _
    refine Finset.mem_filter.2 ⟨mem_Sols.2 ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0 < x.1
      exact ha
    · show 0 < x.2.1 - x.2.2.2
      omega
    · show 0 < x.1 + x.2.2.1
      omega
    · show 0 < x.2.2.2
      exact hd
    · show x.1 * (x.2.1 - x.2.2.2) + (x.1 + x.2.2.1) * x.2.2.2 = N
      omega
    · show x.1 < x.1 + x.2.2.1
      omega
  · intro y hy
    obtain ⟨hyS, hlt⟩ := Finset.mem_filter.1 hy
    obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hyS
    replace hlt : y.1 < y.2.2.1 := hlt
    have e1 : y.1 * (y.2.1 + y.2.2.2) = y.1 * y.2.1 + y.1 * y.2.2.2 := Nat.mul_add _ _ _
    have e2 : (y.2.2.1 - y.1) * y.2.2.2 + y.1 * y.2.2.2 = y.2.2.1 * y.2.2.2 := by
      rw [← Nat.add_mul]
      congr 1
      omega
    refine Finset.mem_filter.2 ⟨mem_Sols.2 ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0 < y.1
      exact ha
    · show 0 < y.2.1 + y.2.2.2
      omega
    · show 0 < y.2.2.1 - y.1
      omega
    · show 0 < y.2.2.2
      exact hd
    · show y.1 * (y.2.1 + y.2.2.2) + (y.2.2.1 - y.1) * y.2.2.2 = N
      omega
    · show y.2.2.2 < y.2.1 + y.2.2.2
      omega
  · intro x hx
    obtain ⟨_, hlt⟩ := Finset.mem_filter.1 hx
    replace hlt : x.2.2.2 < x.2.1 := hlt
    show (x.1, x.2.1 - x.2.2.2 + x.2.2.2, x.1 + x.2.2.1 - x.1, x.2.2.2) = x
    have h1 : x.2.1 - x.2.2.2 + x.2.2.2 = x.2.1 := by omega
    have h2 : x.1 + x.2.2.1 - x.1 = x.2.2.1 := by omega
    rw [h1, h2]
  · intro y hy
    obtain ⟨_, hlt⟩ := Finset.mem_filter.1 hy
    replace hlt : y.1 < y.2.2.1 := hlt
    show (y.1, y.2.1 + y.2.2.2 - y.2.2.2, y.1 + (y.2.2.1 - y.1), y.2.2.2) = y
    have h1 : y.2.1 + y.2.2.2 - y.2.2.2 = y.2.1 := by omega
    have h2 : y.1 + (y.2.2.1 - y.1) = y.2.2.1 := by omega
    rw [h1, h2]
  · intro x _
    rfl

theorem sum_psiSub (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → β) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
        F (x.2.2.1, x.2.1 + x.2.2.2, x.1 - x.2.2.1, x.2.1)
      = ∑ y ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), F y := by
  refine Finset.sum_nbij' (i := fun x => (x.2.2.1, x.2.1 + x.2.2.2, x.1 - x.2.2.1, x.2.1))
    (j := fun y => (y.1 + y.2.2.1, y.2.2.2, y.1, y.2.1 - y.2.2.2)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxS, hlt⟩ := Finset.mem_filter.1 hx
    obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hxS
    replace hlt : x.2.2.1 < x.1 := hlt
    have e1 : x.2.2.1 * (x.2.1 + x.2.2.2) = x.2.2.1 * x.2.1 + x.2.2.1 * x.2.2.2 :=
      Nat.mul_add _ _ _
    have e2 : (x.1 - x.2.2.1) * x.2.1 + x.2.2.1 * x.2.1 = x.1 * x.2.1 := by
      rw [← Nat.add_mul]
      congr 1
      omega
    refine Finset.mem_filter.2 ⟨mem_Sols.2 ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0 < x.2.2.1
      exact hc
    · show 0 < x.2.1 + x.2.2.2
      omega
    · show 0 < x.1 - x.2.2.1
      omega
    · show 0 < x.2.1
      exact hb
    · show x.2.2.1 * (x.2.1 + x.2.2.2) + (x.1 - x.2.2.1) * x.2.1 = N
      omega
    · show x.2.1 < x.2.1 + x.2.2.2
      omega
  · intro y hy
    obtain ⟨hyS, hlt⟩ := Finset.mem_filter.1 hy
    obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hyS
    replace hlt : y.2.2.2 < y.2.1 := hlt
    have e1 : (y.1 + y.2.2.1) * y.2.2.2 = y.1 * y.2.2.2 + y.2.2.1 * y.2.2.2 :=
      Nat.add_mul _ _ _
    have e2 : y.1 * (y.2.1 - y.2.2.2) + y.1 * y.2.2.2 = y.1 * y.2.1 := by
      rw [← Nat.mul_add]
      congr 1
      omega
    refine Finset.mem_filter.2 ⟨mem_Sols.2 ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0 < y.1 + y.2.2.1
      omega
    · show 0 < y.2.2.2
      exact hd
    · show 0 < y.1
      exact ha
    · show 0 < y.2.1 - y.2.2.2
      omega
    · show (y.1 + y.2.2.1) * y.2.2.2 + y.1 * (y.2.1 - y.2.2.2) = N
      omega
    · show y.1 < y.1 + y.2.2.1
      omega
  · intro x hx
    obtain ⟨_, hlt⟩ := Finset.mem_filter.1 hx
    replace hlt : x.2.2.1 < x.1 := hlt
    show (x.2.2.1 + (x.1 - x.2.2.1), x.2.1, x.2.2.1, x.2.1 + x.2.2.2 - x.2.1) = x
    have h1 : x.2.2.1 + (x.1 - x.2.2.1) = x.1 := by omega
    have h2 : x.2.1 + x.2.2.2 - x.2.1 = x.2.2.2 := by omega
    rw [h1, h2]
  · intro y hy
    obtain ⟨_, hlt⟩ := Finset.mem_filter.1 hy
    replace hlt : y.2.2.2 < y.2.1 := hlt
    show (y.1, y.2.2.2 + (y.2.1 - y.2.2.2), y.1 + y.2.2.1 - y.1, y.2.2.2) = y
    have h1 : y.2.2.2 + (y.2.1 - y.2.2.2) = y.2.1 := by omega
    have h2 : y.1 + y.2.2.1 - y.1 = y.2.2.1 := by omega
    rw [h1, h2]
  · intro x _
    rfl

theorem sum_slice_codiag (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → β) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.1 = x.2.2.2), F x
      = ∑ p ∈ N.divisorsAntidiagonal, ∑ a ∈ Finset.Ico 1 p.2, F (a, p.1, p.2 - a, p.1) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun x => ⟨(x.2.1, x.1 + x.2.2.1), x.1⟩)
    (j := fun y => (y.2, y.1.1, y.1.2 - y.2, y.1.1)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxS, hx24⟩ := Finset.mem_filter.1 hx
    obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hxS
    replace hx24 : x.2.1 = x.2.2.2 := hx24
    have e1 : x.2.1 * (x.1 + x.2.2.1) = x.2.1 * x.1 + x.2.1 * x.2.2.1 := Nat.mul_add _ _ _
    have e2 : x.1 * x.2.1 = x.2.1 * x.1 := Nat.mul_comm _ _
    have e3 : x.2.2.1 * x.2.2.2 = x.2.1 * x.2.2.1 := by
      rw [← hx24]
      exact Nat.mul_comm _ _
    have heq2 : x.2.1 * (x.1 + x.2.2.1) = N := by omega
    have hN : N ≠ 0 := by
      have hpos : 0 < x.2.1 * (x.1 + x.2.2.1) := Nat.mul_pos hb (by omega)
      omega
    refine Finset.mem_sigma.2 ⟨Nat.mem_divisorsAntidiagonal.2 ⟨heq2, hN⟩, ?_⟩
    refine Finset.mem_Ico.2 ⟨ha, ?_⟩
    show x.1 < x.1 + x.2.2.1
    omega
  · intro y hy
    obtain ⟨hp, ha⟩ := Finset.mem_sigma.1 hy
    obtain ⟨heq, hN⟩ := Nat.mem_divisorsAntidiagonal.1 hp
    obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.1 ha
    have hy11 : 0 < y.1.1 := by
      rcases Nat.eq_zero_or_pos y.1.1 with h | h
      · exfalso
        apply hN
        rw [← heq, h, Nat.zero_mul]
      · exact h
    refine Finset.mem_filter.2 ⟨mem_Sols.2 ⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · show 0 < y.2
      exact ha1
    · show 0 < y.1.1
      exact hy11
    · show 0 < y.1.2 - y.2
      omega
    · show 0 < y.1.1
      exact hy11
    · show y.2 * y.1.1 + (y.1.2 - y.2) * y.1.1 = N
      rw [← Nat.add_mul, Nat.add_sub_cancel' ha2.le, Nat.mul_comm]
      exact heq
  · intro x hx
    obtain ⟨hxS, hx24⟩ := Finset.mem_filter.1 hx
    replace hx24 : x.2.1 = x.2.2.2 := hx24
    show (x.1, x.2.1, x.1 + x.2.2.1 - x.1, x.2.1) = x
    have h1 : x.1 + x.2.2.1 - x.1 = x.2.2.1 := by omega
    rw [h1]
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hx24))
  · intro y hy
    obtain ⟨hp, ha⟩ := Finset.mem_sigma.1 hy
    obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.1 ha
    have h2 : y.2 + (y.1.2 - y.2) = y.1.2 := by omega
    show (⟨(y.1.1, y.2 + (y.1.2 - y.2)), y.2⟩ : (_ : ℕ × ℕ) × ℕ) = y
    rw [h2]
  · intro x hx
    obtain ⟨hxS, hx24⟩ := Finset.mem_filter.1 hx
    replace hx24 : x.2.1 = x.2.2.2 := hx24
    have htup : (x.1, x.2.1, x.1 + x.2.2.1 - x.1, x.2.1) = x := by
      have h1 : x.1 + x.2.2.1 - x.1 = x.2.2.1 := by omega
      rw [h1]
      exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hx24))
    exact (congrArg F htup).symm

theorem sum_swap₁_total (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → β) :
    ∑ x ∈ Sols N, F x = ∑ x ∈ Sols N, F (swap₁ x) := by
  refine Finset.sum_nbij' (i := swap₁) (j := swap₁) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact swap₁_mem_Sols hx
  · intro x hx
    exact swap₁_mem_Sols hx
  · intro x _
    exact swap₁_swap₁ x
  · intro x _
    exact swap₁_swap₁ x
  · intro x _
    exact (congrArg F (swap₁_swap₁ x)).symm

theorem sum_swap₁_filter_bd (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → β) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), F x
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), F (swap₁ x) := by
  refine Finset.sum_nbij' (i := swap₁) (j := swap₁) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxS, hcond⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨swap₁_mem_Sols hxS, hcond⟩
  · intro x hx
    obtain ⟨hxS, hcond⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨swap₁_mem_Sols hxS, hcond⟩
  · intro x _
    exact swap₁_swap₁ x
  · intro x _
    exact swap₁_swap₁ x
  · intro x _
    exact (congrArg F (swap₁_swap₁ x)).symm

theorem sum_swap₁_filter_ac (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → β) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), F x
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), F (swap₁ x) := by
  refine Finset.sum_nbij' (i := swap₁) (j := swap₁) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxS, hcond⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨swap₁_mem_Sols hxS, hcond⟩
  · intro x hx
    obtain ⟨hxS, hcond⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨swap₁_mem_Sols hxS, hcond⟩
  · intro x _
    exact swap₁_swap₁ x
  · intro x _
    exact swap₁_swap₁ x
  · intro x _
    exact (congrArg F (swap₁_swap₁ x)).symm

theorem sum_split_bd (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → β) :
    ∑ x ∈ Sols N, F x
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), F x
        + ∑ x ∈ (Sols N).filter (fun x => x.2.1 = x.2.2.2), F x
        + ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), F x := by
  classical
  have h1 := Finset.sum_filter_add_sum_filter_not (Sols N) (fun x => x.2.2.2 < x.2.1) F
  have h2 := Finset.sum_filter_add_sum_filter_not
    ((Sols N).filter (fun x => ¬ x.2.2.2 < x.2.1)) (fun x => x.2.1 = x.2.2.2) F
  have e1 : ((Sols N).filter (fun x => ¬ x.2.2.2 < x.2.1)).filter (fun x => x.2.1 = x.2.2.2)
      = (Sols N).filter (fun x => x.2.1 = x.2.2.2) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by constructor <;> intro hx <;> omega)
  have e2 : ((Sols N).filter (fun x => ¬ x.2.2.2 < x.2.1)).filter (fun x => ¬ x.2.1 = x.2.2.2)
      = (Sols N).filter (fun x => x.2.1 < x.2.2.2) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by constructor <;> intro hx <;> omega)
  rw [e1, e2] at h2
  rw [← h1, ← h2]
  exact (add_assoc _ _ _).symm

theorem sum_split_ac (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → β) :
    ∑ x ∈ Sols N, F x
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), F x
        + ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), F x
        + ∑ x ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), F x := by
  classical
  have h1 := Finset.sum_filter_add_sum_filter_not (Sols N) (fun x => x.2.2.1 < x.1) F
  have h2 := Finset.sum_filter_add_sum_filter_not
    ((Sols N).filter (fun x => ¬ x.2.2.1 < x.1)) (fun x => x.1 = x.2.2.1) F
  have e1 : ((Sols N).filter (fun x => ¬ x.2.2.1 < x.1)).filter (fun x => x.1 = x.2.2.1)
      = (Sols N).filter (fun x => x.1 = x.2.2.1) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by constructor <;> intro hx <;> omega)
  have e2 : ((Sols N).filter (fun x => ¬ x.2.2.1 < x.1)).filter (fun x => ¬ x.1 = x.2.2.1)
      = (Sols N).filter (fun x => x.1 < x.2.2.1) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by constructor <;> intro hx <;> omega)
  rw [e1, e2] at h2
  rw [← h1, ← h2]
  exact (add_assoc _ _ _).symm

end Engine
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section Faulhaber

variable {A : Type*} [CommRing A]

theorem six_mul_sum_Ico_mul_rev_cast (m : ℕ) :
    (6 : A) * ∑ a ∈ Finset.Ico 1 m, (a : A) * ((m - a : ℕ) : A) = (m : A) ^ 3 - (m : A) := by
  have hsum : ∑ a ∈ Finset.Ico 1 m, (a : A) * ((m - a : ℕ) : A)
      = ∑ a ∈ Finset.Ico 1 m, (a : A) * ((m : A) - (a : A)) :=
    Finset.sum_congr rfl (fun a ha => by rw [Nat.cast_sub (Finset.mem_Ico.1 ha).2.le])
  rw [hsum]
  have key := congrArg (fun z : ℤ => (z : A)) (six_mul_sum_Ico_mul_rev m)
  push_cast at key
  linear_combination key

theorem sum_Ico_weight_reflect (f : ℤ → A) (m : ℕ) :
    ∑ a ∈ Finset.Ico 1 m, (a : A) * (m : A) * f ((m - a : ℕ) : ℤ)
      = ∑ k ∈ Finset.Ico 1 m, (m : A) * ((m : A) - (k : A)) * f (k : ℤ) := by
  refine Finset.sum_nbij' (i := fun a => m - a) (j := fun k => m - k) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ha
    show m - a ∈ Finset.Ico 1 m
    exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
  · intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
    show m - k ∈ Finset.Ico 1 m
    exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ha
    show m - (m - a) = a
    omega
  · intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
    show m - (m - k) = k
    omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ha
    show (a : A) * (m : A) * f ((m - a : ℕ) : ℤ)
      = (m : A) * ((m : A) - ((m - a : ℕ) : A)) * f ((m - a : ℕ) : ℤ)
    have h4 : ((m - a : ℕ) : A) = (m : A) - (a : A) := Nat.cast_sub h2.le
    rw [h4]
    ring

end Faulhaber
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section PhiGeneral

variable {A : Type*} [CommRing A]

theorem phi_general (f : ℤ → A) (hf0 : f 0 = 0) (hfneg : ∀ a : ℤ, f (-a) = f a) (M : ℕ) :
    6 * ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) *
        (f ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + f ((x.1 : ℤ) - (x.2.2.1 : ℤ))
          - 2 * f (x.1 : ℤ) - 2 * f (x.2.2.1 : ℤ))
      = ∑ δ ∈ M.divisors, ((δ : A) ^ 3 - (δ : A)) * f (δ : ℤ)
        - 12 * ∑ δ ∈ M.divisors, ∑ k ∈ Finset.Ico 1 δ,
            (δ : A) * ((δ : A) - (k : A)) * f (k : ℤ) := by
  classical

  have hexpand : ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) *
        (f ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + f ((x.1 : ℤ) - (x.2.2.1 : ℤ))
          - 2 * f (x.1 : ℤ) - 2 * f (x.2.2.1 : ℤ))
      = ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ))
        + ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ))
        - 2 * ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * f (x.1 : ℤ)
        - 2 * ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)

  have hsplitT1 : ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ))
      = ∑ x ∈ (Sols M).filter (fun x => x.2.2.2 < x.2.1),
          (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ))
        + ∑ x ∈ (Sols M).filter (fun x => x.2.1 = x.2.2.2),
          (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ))
        + ∑ x ∈ (Sols M).filter (fun x => x.2.1 < x.2.2.2),
          (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ)) :=
    sum_split_bd M (fun x => (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ)))
  have hfold1 : ∑ x ∈ (Sols M).filter (fun x => x.2.1 < x.2.2.2),
        (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ))
      = ∑ x ∈ (Sols M).filter (fun x => x.2.2.2 < x.2.1),
        (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ)) := by
    refine Eq.trans (sum_swap₁_filter_bd M
      (fun x => (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ)))) ?_
    refine Finset.sum_congr rfl (fun x _ => ?_)
    show (x.2.2.1 : A) * (x.1 : A) * f ((x.2.2.1 : ℤ) + (x.1 : ℤ))
      = (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ))
    rw [add_comm ((x.2.2.1 : ℤ)) ((x.1 : ℤ))]
    ring
  have hdiag1 : 6 * ∑ x ∈ (Sols M).filter (fun x => x.2.1 = x.2.2.2),
        (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ))
      = ∑ δ ∈ M.divisors, ((δ : A) ^ 3 - (δ : A)) * f (δ : ℤ) := by
    have hslice : ∑ x ∈ (Sols M).filter (fun x => x.2.1 = x.2.2.2),
          (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ))
        = ∑ p ∈ M.divisorsAntidiagonal, ∑ a ∈ Finset.Ico 1 p.2,
            (a : A) * ((p.2 - a : ℕ) : A) * f (p.2 : ℤ) := by
      refine Eq.trans (sum_slice_codiag M
        (fun x => (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ)))) ?_
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun a ha => ?_))
      obtain ⟨_, ha2⟩ := Finset.mem_Ico.1 ha
      show (a : A) * ((p.2 - a : ℕ) : A) * f ((a : ℤ) + ((p.2 - a : ℕ) : ℤ))
        = (a : A) * ((p.2 - a : ℕ) : A) * f (p.2 : ℤ)
      have harg : (a : ℤ) + ((p.2 - a : ℕ) : ℤ) = (p.2 : ℤ) := by omega
      rw [harg]
    rw [hslice, Finset.mul_sum]
    have hpoint : ∀ p ∈ M.divisorsAntidiagonal,
        6 * ∑ a ∈ Finset.Ico 1 p.2, (a : A) * ((p.2 - a : ℕ) : A) * f (p.2 : ℤ)
          = ((p.2 : A) ^ 3 - (p.2 : A)) * f (p.2 : ℤ) := by
      intro p _
      rw [← Finset.sum_mul, ← mul_assoc, six_mul_sum_Ico_mul_rev_cast]
    exact Eq.trans (Finset.sum_congr rfl hpoint)
      (Nat.sum_divisorsAntidiagonal'
        (f := fun (_ : ℕ) δ => ((δ : A) ^ 3 - (δ : A)) * f (δ : ℤ)) (n := M))
  have hPint : ∑ x ∈ (Sols M).filter (fun x => x.2.2.2 < x.2.1),
        (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ))
      = ∑ y ∈ (Sols M).filter (fun x => x.1 < x.2.2.1),
        (y.1 : A) * ((y.2.2.1 : A) - (y.1 : A)) * f (y.2.2.1 : ℤ) := by
    refine Eq.trans (Finset.sum_congr rfl (fun x _ => ?_)) (sum_psiAdd M
      (fun y => (y.1 : A) * ((y.2.2.1 : A) - (y.1 : A)) * f (y.2.2.1 : ℤ)))
    show (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) + (x.2.2.1 : ℤ))
      = (x.1 : A) * (((x.1 + x.2.2.1 : ℕ) : A) - (x.1 : A)) * f ((x.1 + x.2.2.1 : ℕ) : ℤ)
    have h1 : ((x.1 + x.2.2.1 : ℕ) : A) - (x.1 : A) = (x.2.2.1 : A) := by
      push_cast
      ring
    have h2 : ((x.1 + x.2.2.1 : ℕ) : ℤ) = (x.1 : ℤ) + (x.2.2.1 : ℤ) := by
      push_cast
      ring
    rw [h1, h2]
  have hW6 : ∑ y ∈ (Sols M).filter (fun x => x.1 < x.2.2.1),
        (y.1 : A) * ((y.2.2.1 : A) - (y.1 : A)) * f (y.2.2.1 : ℤ)
      = ∑ y ∈ (Sols M).filter (fun x => x.1 < x.2.2.1),
          (y.1 : A) * (y.2.2.1 : A) * f (y.2.2.1 : ℤ)
        - ∑ y ∈ (Sols M).filter (fun x => x.1 < x.2.2.1),
          (y.1 : A) * (y.1 : A) * f (y.2.2.1 : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)

  have hsplitT2 : ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ))
      = ∑ x ∈ (Sols M).filter (fun x => x.2.2.1 < x.1),
          (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ))
        + ∑ x ∈ (Sols M).filter (fun x => x.1 = x.2.2.1),
          (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ))
        + ∑ x ∈ (Sols M).filter (fun x => x.1 < x.2.2.1),
          (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ)) :=
    sum_split_ac M (fun x => (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ)))
  have hdiag2 : ∑ x ∈ (Sols M).filter (fun x => x.1 = x.2.2.1),
        (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ)) = 0 := by
    refine Finset.sum_eq_zero (fun x hx => ?_)
    have hxe : x.1 = x.2.2.1 := (Finset.mem_filter.1 hx).2
    rw [hxe, sub_self, hf0, mul_zero]
  have hfold2 : ∑ x ∈ (Sols M).filter (fun x => x.1 < x.2.2.1),
        (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ))
      = ∑ x ∈ (Sols M).filter (fun x => x.2.2.1 < x.1),
        (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ)) := by
    refine Eq.trans (sum_swap₁_filter_ac M
      (fun x => (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ)))) ?_
    refine Finset.sum_congr rfl (fun x _ => ?_)
    show (x.2.2.1 : A) * (x.1 : A) * f ((x.2.2.1 : ℤ) - (x.1 : ℤ))
      = (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ))
    rw [show (x.2.2.1 : ℤ) - (x.1 : ℤ) = -((x.1 : ℤ) - (x.2.2.1 : ℤ)) from by ring, hfneg]
    ring
  have hQ : ∑ x ∈ (Sols M).filter (fun x => x.2.2.1 < x.1),
        (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ))
      = ∑ y ∈ (Sols M).filter (fun x => x.2.2.2 < x.2.1),
        (y.1 : A) * ((y.1 : A) + (y.2.2.1 : A)) * f (y.2.2.1 : ℤ) := by
    refine Eq.trans (Finset.sum_congr rfl (fun x hx => ?_)) (sum_psiSub M
      (fun y => (y.1 : A) * ((y.1 : A) + (y.2.2.1 : A)) * f (y.2.2.1 : ℤ)))
    have hlt : x.2.2.1 < x.1 := (Finset.mem_filter.1 hx).2
    show (x.1 : A) * (x.2.2.1 : A) * f ((x.1 : ℤ) - (x.2.2.1 : ℤ))
      = (x.2.2.1 : A) * ((x.2.2.1 : A) + ((x.1 - x.2.2.1 : ℕ) : A)) * f ((x.1 - x.2.2.1 : ℕ) : ℤ)
    have h1 : (x.2.2.1 : A) + ((x.1 - x.2.2.1 : ℕ) : A) = (x.1 : A) := by
      rw [Nat.cast_sub hlt.le]
      ring
    have h2 : ((x.1 - x.2.2.1 : ℕ) : ℤ) = (x.1 : ℤ) - (x.2.2.1 : ℤ) := Nat.cast_sub hlt.le
    rw [h1, h2]
    ring

  have hswap34 : ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * f (x.1 : ℤ)
      = ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ) := by
    refine Eq.trans (sum_swap₁_total M
      (fun x => (x.1 : A) * (x.2.2.1 : A) * f (x.1 : ℤ))) ?_
    refine Finset.sum_congr rfl (fun x _ => ?_)
    show (x.2.2.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ)
      = (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ)
    ring

  have hU : ∑ δ ∈ M.divisors, ∑ k ∈ Finset.Ico 1 δ, (δ : A) * ((δ : A) - (k : A)) * f (k : ℤ)
      = ∑ x ∈ (Sols M).filter (fun x => x.2.1 = x.2.2.2),
        (x.1 : A) * ((x.1 : A) + (x.2.2.1 : A)) * f (x.2.2.1 : ℤ) := by
    have hslice : ∑ x ∈ (Sols M).filter (fun x => x.2.1 = x.2.2.2),
          (x.1 : A) * ((x.1 : A) + (x.2.2.1 : A)) * f (x.2.2.1 : ℤ)
        = ∑ p ∈ M.divisorsAntidiagonal, ∑ a ∈ Finset.Ico 1 p.2,
            (a : A) * (p.2 : A) * f ((p.2 - a : ℕ) : ℤ) := by
      refine Eq.trans (sum_slice_codiag M
        (fun x => (x.1 : A) * ((x.1 : A) + (x.2.2.1 : A)) * f (x.2.2.1 : ℤ))) ?_
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun a ha => ?_))
      obtain ⟨_, ha2⟩ := Finset.mem_Ico.1 ha
      show (a : A) * ((a : A) + ((p.2 - a : ℕ) : A)) * f ((p.2 - a : ℕ) : ℤ)
        = (a : A) * (p.2 : A) * f ((p.2 - a : ℕ) : ℤ)
      have h1 : (a : A) + ((p.2 - a : ℕ) : A) = (p.2 : A) := by
        rw [Nat.cast_sub ha2.le]
        ring
      rw [h1]
    have hreflect : ∀ p ∈ M.divisorsAntidiagonal,
        (∑ a ∈ Finset.Ico 1 p.2, (a : A) * (p.2 : A) * f ((p.2 - a : ℕ) : ℤ))
          = ∑ k ∈ Finset.Ico 1 p.2, (p.2 : A) * ((p.2 : A) - (k : A)) * f (k : ℤ) :=
      fun p _ => sum_Ico_weight_reflect f p.2
    refine Eq.trans ?_ hslice.symm
    refine Eq.trans ?_ (Finset.sum_congr rfl hreflect).symm
    exact (Nat.sum_divisorsAntidiagonal'
      (f := fun (_ : ℕ) δ => ∑ k ∈ Finset.Ico 1 δ, (δ : A) * ((δ : A) - (k : A)) * f (k : ℤ))
      (n := M)).symm

  have hE1 : ∑ x ∈ (Sols M).filter (fun x => x.2.2.1 < x.1),
        ((x.1 : A) - (x.2.2.1 : A)) * (x.1 : A) * f (x.2.2.1 : ℤ)
      = ∑ y ∈ (Sols M).filter (fun x => x.2.1 < x.2.2.2),
        (y.1 : A) * ((y.1 : A) + (y.2.2.1 : A)) * f (y.2.2.1 : ℤ) := by
    refine Eq.trans (Finset.sum_congr rfl (fun x hx => ?_)) (sum_euclidStep M
      (fun y => (y.1 : A) * ((y.1 : A) + (y.2.2.1 : A)) * f (y.2.2.1 : ℤ)))
    have hlt : x.2.2.1 < x.1 := (Finset.mem_filter.1 hx).2
    show ((x.1 : A) - (x.2.2.1 : A)) * (x.1 : A) * f (x.2.2.1 : ℤ)
      = ((x.1 - x.2.2.1 : ℕ) : A) * (((x.1 - x.2.2.1 : ℕ) : A) + (x.2.2.1 : A)) * f (x.2.2.1 : ℤ)
    have h1 : ((x.1 - x.2.2.1 : ℕ) : A) = (x.1 : A) - (x.2.2.1 : A) := Nat.cast_sub hlt.le
    rw [h1]
    ring
  have hW8 : ∑ x ∈ (Sols M).filter (fun x => x.2.2.1 < x.1),
        ((x.1 : A) - (x.2.2.1 : A)) * (x.1 : A) * f (x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols M).filter (fun x => x.2.2.1 < x.1),
          (x.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ)
        - ∑ x ∈ (Sols M).filter (fun x => x.2.2.1 < x.1),
          (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)

  have hW7db : ∑ y ∈ (Sols M).filter (fun x => x.2.2.2 < x.2.1),
        (y.1 : A) * ((y.1 : A) + (y.2.2.1 : A)) * f (y.2.2.1 : ℤ)
      = ∑ y ∈ (Sols M).filter (fun x => x.2.2.2 < x.2.1),
          (y.1 : A) * (y.2.2.1 : A) * f (y.2.2.1 : ℤ)
        + ∑ y ∈ (Sols M).filter (fun x => x.2.2.2 < x.2.1),
          (y.1 : A) * (y.1 : A) * f (y.2.2.1 : ℤ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  have hW7eq : ∑ y ∈ (Sols M).filter (fun x => x.2.1 = x.2.2.2),
        (y.1 : A) * ((y.1 : A) + (y.2.2.1 : A)) * f (y.2.2.1 : ℤ)
      = ∑ y ∈ (Sols M).filter (fun x => x.2.1 = x.2.2.2),
          (y.1 : A) * (y.2.2.1 : A) * f (y.2.2.1 : ℤ)
        + ∑ y ∈ (Sols M).filter (fun x => x.2.1 = x.2.2.2),
          (y.1 : A) * (y.1 : A) * f (y.2.2.1 : ℤ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  have hW7bd : ∑ y ∈ (Sols M).filter (fun x => x.2.1 < x.2.2.2),
        (y.1 : A) * ((y.1 : A) + (y.2.2.1 : A)) * f (y.2.2.1 : ℤ)
      = ∑ y ∈ (Sols M).filter (fun x => x.2.1 < x.2.2.2),
          (y.1 : A) * (y.2.2.1 : A) * f (y.2.2.1 : ℤ)
        + ∑ y ∈ (Sols M).filter (fun x => x.2.1 < x.2.2.2),
          (y.1 : A) * (y.1 : A) * f (y.2.2.1 : ℤ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)

  have hsplit4ac : ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols M).filter (fun x => x.2.2.1 < x.1),
          (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ)
        + ∑ x ∈ (Sols M).filter (fun x => x.1 = x.2.2.1),
          (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ)
        + ∑ x ∈ (Sols M).filter (fun x => x.1 < x.2.2.1),
          (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ) :=
    sum_split_ac M (fun x => (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ))
  have hsplit4bd : ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols M).filter (fun x => x.2.2.2 < x.2.1),
          (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ)
        + ∑ x ∈ (Sols M).filter (fun x => x.2.1 = x.2.2.2),
          (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ)
        + ∑ x ∈ (Sols M).filter (fun x => x.2.1 < x.2.2.2),
          (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ) :=
    sum_split_bd M (fun x => (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ))
  have hsplit9ac : ∑ x ∈ Sols M, (x.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols M).filter (fun x => x.2.2.1 < x.1),
          (x.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ)
        + ∑ x ∈ (Sols M).filter (fun x => x.1 = x.2.2.1),
          (x.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ)
        + ∑ x ∈ (Sols M).filter (fun x => x.1 < x.2.2.1),
          (x.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ) :=
    sum_split_ac M (fun x => (x.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ))
  have hsplit9bd : ∑ x ∈ Sols M, (x.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols M).filter (fun x => x.2.2.2 < x.2.1),
          (x.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ)
        + ∑ x ∈ (Sols M).filter (fun x => x.2.1 = x.2.2.2),
          (x.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ)
        + ∑ x ∈ (Sols M).filter (fun x => x.2.1 < x.2.2.2),
          (x.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ) :=
    sum_split_bd M (fun x => (x.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ))
  have hdiag9 : ∑ x ∈ (Sols M).filter (fun x => x.1 = x.2.2.1),
        (x.1 : A) * (x.1 : A) * f (x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols M).filter (fun x => x.1 = x.2.2.1),
        (x.1 : A) * (x.2.2.1 : A) * f (x.2.2.1 : ℤ) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxe : x.1 = x.2.2.1 := (Finset.mem_filter.1 hx).2
    rw [hxe]

  rw [hexpand]
  linear_combination 6 * hsplitT1 + 6 * hfold1 + hdiag1 + 12 * hPint + 12 * hW6
    + 6 * hsplitT2 + 6 * hdiag2 + 6 * hfold2 + 12 * hQ + 12 * hW7db - 12 * hswap34
    + 12 * hU + 12 * hW7eq + 12 * hE1 - 12 * hW8 + 12 * hW7bd - 12 * hsplit4ac
    - 12 * hsplit4bd + 12 * hsplit9ac - 12 * hsplit9bd + 12 * hdiag9

end PhiGeneral
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section PhiTate

variable {K : Type*} [NontriviallyNormedField K]

theorem xCoeff_eq_sum_mul_Fz (v : K) (N : ℕ) :
    xCoeff v N = ∑ d ∈ N.divisors, (d : K) * Fz v (d : ℤ) := by
  rw [xCoeff]
  exact Finset.sum_congr rfl (fun d _ => xDivTerm_eq_mul_Fz v d)

theorem phi_identity_fz {v : K} (hv : v ≠ 0) (M : ℕ) :
    (∑ e ∈ M.divisors, (e : K) ^ 3 * Fz v (e : ℤ)) + 12 * (sigma 3 M : K)
      = 6 * cauchyMulInt (xCoeffFull v) (xCoeffFull v) M + xCoeff v M
        + 12 * ∑ d ∈ M.divisors,
            (d : K) * ((d : K) ^ 2
              + ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * Fz v (k : ℤ)) := by

  have hconv : cauchyMulInt (xCoeffFull v) (xCoeffFull v) M
      = ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) *
          (Fz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + Fz v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
            - 2 * Fz v (x.1 : ℤ) - 2 * Fz v (x.2.2.1 : ℤ)) := by
    rw [cauchyMulInt_xx_eq_sum_Sols v M]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz,
      show (x.1 : K) * Fz v (x.1 : ℤ) * ((x.2.2.1 : K) * Fz v (x.2.2.1 : ℤ))
        = (x.1 : K) * (x.2.2.1 : K) * (Fz v (x.1 : ℤ) * Fz v (x.2.2.1 : ℤ)) from by ring,
      Fz_mul_Fz hv]

  have hphi := phi_general (Fz v) (Fz_zero v) (Fz_neg v) M

  have hsplit : ∑ δ ∈ M.divisors, ((δ : K) ^ 3 - (δ : K)) * Fz v (δ : ℤ)
      = ∑ δ ∈ M.divisors, (δ : K) ^ 3 * Fz v (δ : ℤ)
        - ∑ δ ∈ M.divisors, (δ : K) * Fz v (δ : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun δ _ => by ring)

  have hsigma : (sigma 3 M : K) = ∑ d ∈ M.divisors, (d : K) ^ 3 := by
    simp only [sigma]
    push_cast
    rfl

  have htents : ∑ d ∈ M.divisors,
        (d : K) * ((d : K) ^ 2 + ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * Fz v (k : ℤ))
      = ∑ d ∈ M.divisors, (d : K) ^ 3
        + ∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
            (d : K) * ((d : K) - (k : K)) * Fz v (k : ℤ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [mul_add, Finset.mul_sum]
    have hinner : ∀ k ∈ Finset.Ico 1 d,
        (d : K) * (((d - k : ℕ) : K) * Fz v (k : ℤ))
          = (d : K) * ((d : K) - (k : K)) * Fz v (k : ℤ) := by
      intro k hk
      rw [Nat.cast_sub (Finset.mem_Ico.1 hk).2.le]
      ring
    rw [Finset.sum_congr rfl hinner]
    ring

  have hxc := xCoeff_eq_sum_mul_Fz v M

  rw [hconv, hxc, htents, hsigma]
  linear_combination (-1 : K) * hphi - hsplit

theorem phi_identity [CharZero K] {v : K} (hv : v ≠ 0) (M : ℕ) :
    (∑ e ∈ M.divisors, (e : K) ^ 3 * Fz v (e : ℤ)) + 12 * (sigma 3 M : K)
      = 6 * cauchyMulInt (xCoeffFull v) (xCoeffFull v) M + xCoeff v M
        + 12 * ∑ d ∈ M.divisors, (d : K) * tent v d := by
  by_cases hv1 : v = 1
  ·
    subst hv1
    have hFz : ∀ a : ℤ, Fz (1 : K) a = 0 := by
      intro a
      simp only [Fz, one_zpow]
      norm_num
    have hxc : ∀ N : ℕ, xCoeff (1 : K) N = 0 := by
      intro N
      rw [xCoeff_eq_sum_mul_Fz]
      refine Finset.sum_eq_zero (fun d _ => ?_)
      rw [hFz, mul_zero]
    have hconv : cauchyMulInt (xCoeffFull (1 : K)) (xCoeffFull (1 : K)) M = 0 := by
      rw [cauchyMulInt]
      refine Finset.sum_eq_zero (fun i hi => ?_)
      have hi1 : 0 < i := (Finset.mem_Ico.1 hi).1
      rw [xCoeffFull_of_pos (1 : K) hi1, hxc, zero_mul]
    have htent : ∀ d : ℕ, tent (1 : K) d = (d : K) ^ 2 := by
      intro d
      simp [tent]
    have hLHS : (∑ e ∈ M.divisors, (e : K) ^ 3 * Fz (1 : K) (e : ℤ)) = 0 :=
      Finset.sum_eq_zero (fun e _ => by rw [hFz, mul_zero])
    have htents : ∑ d ∈ M.divisors, (d : K) * tent (1 : K) d
        = ∑ d ∈ M.divisors, (d : K) ^ 3 :=
      Finset.sum_congr rfl (fun d _ => by rw [htent d]; ring)
    have hsigma : (sigma 3 M : K) = ∑ d ∈ M.divisors, (d : K) ^ 3 := by
      simp only [sigma]
      push_cast
      rfl
    rw [hconv, hxc, hLHS, htents, hsigma]
    ring
  ·
    have htent : ∑ d ∈ M.divisors, (d : K) * tent v d
        = ∑ d ∈ M.divisors,
            (d : K) * ((d : K) ^ 2
              + ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * Fz v (k : ℤ)) := by
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [tent_eq_sq_add_sum_Ico hv hv1 d]
    rw [htent]
    exact phi_identity_fz hv M

end PhiTate
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped NNReal

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt cauchyMul_eq_boundary_add_int cauchyMul_cube_eq_boundary_add_int xCoeffFull_of_pos cauchyMulInt_xx_eq_sum_Sols defectCoeff_eq_boundary_add_int Fz Gz Fz_zero Gz_zero Fz_neg Gz_neg Fz_natCast Gz_natCast Fz_mul_Fz Fz_mul_Gz xDivTerm_eq_mul_Fz tent xfun_mul_Fz_eq_tent tent_eq_sq_add_sum_Ico cauchyMul cauchyMul_zero xCoeffFull xCoeffFull_zero a₄Coeff a₄Coeff_zero a₆Coeff xfun yfun pointX pointY term b a₄ curve xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff psifun svComplex LatticeRep OnHalfLattice ks17_A_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v w : K}

section Psifun
@[scoped simp] theorem psifun_zero : psifun (0 : K) = 0 := by simp [psifun, xfun, yfun]

theorem psiCoeffFull_zero_eq_psifun : psiCoeffFull u 0 = psifun u := by
  rw [psiCoeffFull_zero, psifun]

theorem psifun_eq (hw1 : w ≠ 1) : psifun w = w * (1 + w) / (1 - w) ^ 3 := by
  have h1w : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  rw [psifun, xfun, yfun]
  field_simp
  ring

end Psifun
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section PsiGTents

theorem xfun_mul_Gz_mul_Gz (hw0 : w ≠ 0) (hw1 : w ≠ 1) (a b : ℕ) :
    xfun w * (Gz w (a : ℤ) * Gz w (b : ℤ))
      = (w ^ a + 1) * (w ^ b + 1)
          * (∑ i ∈ Finset.range a, w ^ i) * (∑ i ∈ Finset.range b, w ^ i)
          * w * (w ^ a)⁻¹ * (w ^ b)⁻¹ := by
  have h1w : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hwa : w ^ a ≠ 0 := pow_ne_zero a hw0
  have hwb : w ^ b ≠ 0 := pow_ne_zero b hw0
  have ea : (∑ i ∈ Finset.range a, w ^ i) = (w ^ a - 1) / (w - 1) :=
    (eq_div_iff hw1').mpr (geom_sum_mul w a)
  have eb : (∑ i ∈ Finset.range b, w ^ i) = (w ^ b - 1) / (w - 1) :=
    (eq_div_iff hw1').mpr (geom_sum_mul w b)
  rw [Gz_natCast, Gz_natCast, ea, eb, xfun]
  simp only [inv_pow]
  field_simp
  ring

theorem xfun_mul_Fz_mul_Gz (hw0 : w ≠ 0) (hw1 : w ≠ 1) (a b : ℕ) :
    xfun w * (Fz w (a : ℤ) * Gz w (b : ℤ))
      = -((1 - w) * (w ^ b + 1)
          * (∑ i ∈ Finset.range a, w ^ i) ^ 2 * (∑ i ∈ Finset.range b, w ^ i)
          * w * (w ^ a)⁻¹ * (w ^ b)⁻¹) := by
  have h1w : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hwa : w ^ a ≠ 0 := pow_ne_zero a hw0
  have hwb : w ^ b ≠ 0 := pow_ne_zero b hw0
  have ea : (∑ i ∈ Finset.range a, w ^ i) = (w ^ a - 1) / (w - 1) :=
    (eq_div_iff hw1').mpr (geom_sum_mul w a)
  have eb : (∑ i ∈ Finset.range b, w ^ i) = (w ^ b - 1) / (w - 1) :=
    (eq_div_iff hw1').mpr (geom_sum_mul w b)
  rw [Fz_natCast, Gz_natCast, ea, eb, xfun]
  simp only [inv_pow]
  field_simp
  ring

theorem psifun_mul_Fz_mul_Gz (hw0 : w ≠ 0) (hw1 : w ≠ 1) (a b : ℕ) :
    psifun w * (Fz w (a : ℤ) * Gz w (b : ℤ))
      = -((1 + w) * (w ^ b + 1)
          * (∑ i ∈ Finset.range a, w ^ i) ^ 2 * (∑ i ∈ Finset.range b, w ^ i)
          * w * (w ^ a)⁻¹ * (w ^ b)⁻¹) := by
  have h1w : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hwa : w ^ a ≠ 0 := pow_ne_zero a hw0
  have hwb : w ^ b ≠ 0 := pow_ne_zero b hw0
  have ea : (∑ i ∈ Finset.range a, w ^ i) = (w ^ a - 1) / (w - 1) :=
    (eq_div_iff hw1').mpr (geom_sum_mul w a)
  have eb : (∑ i ∈ Finset.range b, w ^ i) = (w ^ b - 1) / (w - 1) :=
    (eq_div_iff hw1').mpr (geom_sum_mul w b)
  rw [Fz_natCast, Gz_natCast, ea, eb, psifun, xfun, yfun]
  simp only [inv_pow]
  field_simp
  ring

theorem psifun_mul_Fz_mul_Fz (hw0 : w ≠ 0) (hw1 : w ≠ 1) (a b : ℕ) :
    psifun w * (Fz w (a : ℤ) * Fz w (b : ℤ))
      = (1 + w) * (1 - w)
          * (∑ i ∈ Finset.range a, w ^ i) ^ 2 * (∑ i ∈ Finset.range b, w ^ i) ^ 2
          * w * (w ^ a)⁻¹ * (w ^ b)⁻¹ := by
  have h1w : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hwa : w ^ a ≠ 0 := pow_ne_zero a hw0
  have hwb : w ^ b ≠ 0 := pow_ne_zero b hw0
  have ea : (∑ i ∈ Finset.range a, w ^ i) = (w ^ a - 1) / (w - 1) :=
    (eq_div_iff hw1').mpr (geom_sum_mul w a)
  have eb : (∑ i ∈ Finset.range b, w ^ i) = (w ^ b - 1) / (w - 1) :=
    (eq_div_iff hw1').mpr (geom_sum_mul w b)
  rw [Fz_natCast, Fz_natCast, ea, eb, psifun, xfun, yfun]
  simp only [inv_pow]
  field_simp
  ring

end PsiGTents
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section InteriorConversion

theorem xCoeff_mul_sub_xCoeff_mul_inv (hu : u ≠ 0) (hv : v ≠ 0) (n : ℕ) :
    xCoeff (u * v) n - xCoeff (u * v⁻¹) n
      = ∑ d ∈ n.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)) := by
  rw [xCoeff, xCoeff, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz, ← mul_sub, Fz_mul_sub_Fz_mul_inv hu hv]

theorem psiCoeffFull_succ_eq_divisorSum_Gz (N : ℕ) :
    psiCoeffFull u (N + 1) = ∑ d ∈ (N + 1).divisors, (d : K) ^ 2 * Gz u (d : ℤ) := by
  rw [psiCoeffFull_succ_eq_divisorSum]
  exact Finset.sum_congr rfl fun d _ => by rw [Gz_natCast]

end InteriorConversion
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section CrossMinus

theorem xfun_sub_mul_Fz_sub_mul_Fz_sub (hu : u ≠ 0) (hv : v ≠ 0) (huvm : u * v ≠ 1)
    (huvd : u * v⁻¹ ≠ 1) (a b : ℕ) :
    (xfun (u * v) - xfun (u * v⁻¹))
        * ((Fz u (a : ℤ) - Fz v (a : ℤ)) * (Fz u (b : ℤ) - Fz v (b : ℤ)))
      = (u ^ a - v ^ a) * (u ^ b - v ^ b)
          * (u * v * (∑ i ∈ Finset.range a, (u * v) ^ i) * (∑ i ∈ Finset.range b, (u * v) ^ i)
              * ((u * v) ^ a)⁻¹ * ((u * v) ^ b)⁻¹)
        - (u ^ a - (v ^ a)⁻¹) * (u ^ b - (v ^ b)⁻¹)
          * (u * v⁻¹ * (∑ i ∈ Finset.range a, (u * v⁻¹) ^ i)
              * (∑ i ∈ Finset.range b, (u * v⁻¹) ^ i)
              * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ b)⁻¹) := by
  have h1 := xfun_mul_mul_Fz_sub_mul_Fz_sub hu hv huvm a b
  have h2 := xfun_mul_inv_mul_Fz_sub_mul_Fz_sub hu hv huvd a b
  linear_combination h1 - h2

theorem xfun_sub_mul_xfun_sub_mul_Fz_sub (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (d : ℕ) :
    (xfun (u * v) - xfun (u * v⁻¹))
        * ((xfun u - xfun v) * (Fz u (d : ℤ) - Fz v (d : ℤ)))
      = -((u - v) * (u ^ d - v ^ d) * (∑ i ∈ Finset.range d, (u * v) ^ i)
            * ((u * v) ^ d)⁻¹ * (xfun u * xfun v))
        + (u - v⁻¹) * (u ^ d - (v ^ d)⁻¹) * (∑ i ∈ Finset.range d, (u * v⁻¹) ^ i)
            * ((u * v⁻¹) ^ d)⁻¹ * (xfun u * xfun v) := by
  have h1 := xfun_mul_mul_xfun_sub_mul_Fz_sub hu0 hv0 hu1 hv1 huvm d
  have h2 := xfun_mul_inv_mul_xfun_sub_mul_Fz_sub hu0 hv0 hu1 hv1 huvd d
  linear_combination h1 - h2

end CrossMinus
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt cauchyMul_eq_boundary_add_int cauchyMul_cube_eq_boundary_add_int xCoeffFull_of_pos cauchyMulInt_xx_eq_sum_Sols defectCoeff_eq_boundary_add_int Fz Gz Fz_zero Gz_zero Fz_neg Gz_neg Fz_natCast Gz_natCast Fz_mul_Fz Fz_mul_Gz xDivTerm_eq_mul_Fz tent xfun_mul_Fz_eq_tent tent_eq_sq_add_sum_Ico cauchyMul cauchyMul_zero xCoeffFull xCoeffFull_zero a₄Coeff a₄Coeff_zero a₆Coeff xfun yfun pointX pointY term b a₄ curve xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff psifun svComplex LatticeRep OnHalfLattice ks17_A_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section Grouping

theorem addDefectDiffCoeff_eq_grouped (u v : K) {M : ℕ} (hM : 0 < M) :
    addDefectDiffCoeff u v M
      = (xfun (u * v) - xfun (u * v⁻¹))
            * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                (fun i => xCoeffFull u i - xCoeffFull v i) M
        + 2 * ((xfun (u * v) - xfun (u * v⁻¹))
            * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M)))
        + (∑ a ∈ Finset.Icc 1 M, (xCoeff (u * v) a - xCoeff (u * v⁻¹) a)
            * cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
                (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))
        + cauchyMul (psiCoeffFull u) (psiCoeffFull v) M := by

  have hcollM := cauchyMul_cross_collect (xCoeffFull (u * v)) (xCoeffFull u) (xCoeffFull v) M
  have hcollD := cauchyMul_cross_collect (xCoeffFull (u * v⁻¹)) (xCoeffFull u) (xCoeffFull v) M

  have hheadM := cauchyMul_eq_head_add_sum_Icc (xCoeffFull (u * v))
    (cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
      (fun i => xCoeffFull u i - xCoeffFull v i)) M
  have hheadD := cauchyMul_eq_head_add_sum_Icc (xCoeffFull (u * v⁻¹))
    (cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
      (fun i => xCoeffFull u i - xCoeffFull v i)) M
  rw [xCoeffFull_zero] at hheadM
  rw [xCoeffFull_zero] at hheadD

  have hinner : cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
      (fun i => xCoeffFull u i - xCoeffFull v i) M
      = (xfun u - xfun v) * (xCoeff u M - xCoeff v M)
        + (xCoeff u M - xCoeff v M) * (xfun u - xfun v)
        + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
            (fun i => xCoeffFull u i - xCoeffFull v i) M := by
    have h := cauchyMul_eq_boundary_add_int (fun i => xCoeffFull u i - xCoeffFull v i)
      (fun i => xCoeffFull u i - xCoeffFull v i) hM
    simpa only [xCoeffFull_zero, xCoeffFull_of_pos u hM, xCoeffFull_of_pos v hM] using h

  have hmerge : (∑ a ∈ Finset.Icc 1 M, xCoeffFull (u * v) a
        * cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
            (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))
      - ∑ a ∈ Finset.Icc 1 M, xCoeffFull (u * v⁻¹) a
          * cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
              (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)
      = ∑ a ∈ Finset.Icc 1 M, (xCoeff (u * v) a - xCoeff (u * v⁻¹) a)
          * cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
              (fun i => xCoeffFull u i - xCoeffFull v i) (M - a) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_Icc] at ha
    rw [xCoeffFull_of_pos (u * v) (show 0 < a by omega),
      xCoeffFull_of_pos (u * v⁻¹) (show 0 < a by omega)]
    ring
  simp only [addDefectDiffCoeff]
  linear_combination (-1 : K) * hcollM + hcollD + hheadM - hheadD
    + (xfun (u * v) - xfun (u * v⁻¹)) * hinner + hmerge

end Grouping
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section FullSplit

theorem addDefectDiffCoeff_eq_boundary_add_int (u v : K) {M : ℕ} (hM : 0 < M) :
    addDefectDiffCoeff u v M
      = (xfun (u * v) - xfun (u * v⁻¹))
            * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                (fun i => xCoeffFull u i - xCoeffFull v i) M
        + 2 * ((xfun (u * v) - xfun (u * v⁻¹))
            * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M)))
        + (xCoeff (u * v) M - xCoeff (u * v⁻¹) M) * (xfun u - xfun v) ^ 2
        + (∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a - xCoeff (u * v⁻¹) a)
            * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a)))
                + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                    (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)))
        + (psifun u * psiCoeffFull v M + psiCoeffFull u M * psifun v
            + cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M) := by

  have hcross : (∑ a ∈ Finset.Icc 1 M, (xCoeff (u * v) a - xCoeff (u * v⁻¹) a)
        * cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
            (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))
      = (xCoeff (u * v) M - xCoeff (u * v⁻¹) M) * (xfun u - xfun v) ^ 2
        + ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a - xCoeff (u * v⁻¹) a)
            * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a)))
                + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                    (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)) := by
    have htop : cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
        (fun i => xCoeffFull u i - xCoeffFull v i) (M - M) = (xfun u - xfun v) ^ 2 := by
      rw [Nat.sub_self, cauchyMul_zero]
      simp only [xCoeffFull_zero]
      ring
    have hsummand : ∀ a ∈ Finset.Ico 1 M,
        (xCoeff (u * v) a - xCoeff (u * v⁻¹) a)
            * cauchyMul (fun i => xCoeffFull u i - xCoeffFull v i)
                (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)
          = (xCoeff (u * v) a - xCoeff (u * v⁻¹) a)
              * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a)))
                  + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                      (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)) := by
      intro a ha
      rw [Finset.mem_Ico] at ha
      have hMa : 0 < M - a := by omega
      rw [cauchyMul_eq_boundary_add_int _ _ hMa]
      simp only [xCoeffFull_zero, xCoeffFull_of_pos u hMa, xCoeffFull_of_pos v hMa]
      ring
    have hset : Finset.Icc 1 M = insert M (Finset.Ico 1 M) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
      omega
    have hMnot : M ∉ Finset.Ico 1 M := by simp
    rw [hset, Finset.sum_insert hMnot, htop, Finset.sum_congr rfl hsummand]

  have hpsi : cauchyMul (psiCoeffFull u) (psiCoeffFull v) M
      = psifun u * psiCoeffFull v M + psiCoeffFull u M * psifun v
        + cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M := by
    rw [cauchyMul_eq_boundary_add_int _ _ hM, psiCoeffFull_zero_eq_psifun,
      psiCoeffFull_zero_eq_psifun]
  linear_combination addDefectDiffCoeff_eq_grouped u v hM + hcross + hpsi

end FullSplit
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section CrossPairGExpansion

private noncomputable def crossGFamOne_BDiffNormalForm (u₀ v₀ : K) (a c i i' : ℕ) : K :=
  u₀ ^ (i + i' + 1)
    * (v₀ ^ (i + i' + 1) * (v₀ ^ (a + c))⁻¹ - v₀ ^ (a + c) * (v₀ ^ (i + i' + 1))⁻¹)

private noncomputable def crossGFamTwo_BDiffNormalForm (u₀ v₀ : K) (a c i i' : ℕ) : K :=
  u₀ ^ (i + i' + 1) * (u₀ ^ c)⁻¹
    * (v₀ ^ (i + i' + 1) * (v₀ ^ a)⁻¹ - v₀ ^ a * (v₀ ^ (i + i' + 1))⁻¹)

private noncomputable def crossGFamThree_BDiffNormalForm (u₀ v₀ : K) (a c i i' : ℕ) : K :=
  u₀ ^ (i + i' + 1) * (u₀ ^ a)⁻¹
    * (v₀ ^ (i + i' + 1) * (v₀ ^ c)⁻¹ - v₀ ^ c * (v₀ ^ (i + i' + 1))⁻¹)

private noncomputable def crossGFamFour_BDiffNormalForm (u₀ v₀ : K) (a c i i' : ℕ) : K :=
  u₀ ^ (i + i' + 1) * (u₀ ^ (a + c))⁻¹ * (v₀ ^ (i + i' + 1) - (v₀ ^ (i + i' + 1))⁻¹)

set_option maxHeartbeats 3200000 in

private theorem crossGPair_summand_BDiffNormalForm (hu0 : u ≠ 0) (hv0 : v ≠ 0) (a c i i' : ℕ) :
    (u ^ a - v ^ a) * (u ^ c - v ^ c)
        * (u * v * ((u * v) ^ a)⁻¹ * ((u * v) ^ c)⁻¹) * ((u * v) ^ i * (u * v) ^ i')
      - (u ^ a - (v ^ a)⁻¹) * (u ^ c - (v ^ c)⁻¹)
          * (u * v⁻¹ * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ c)⁻¹)
          * ((u * v⁻¹) ^ i * (u * v⁻¹) ^ i')
    = crossGFamOne_BDiffNormalForm u v a c i i' - crossGFamTwo_BDiffNormalForm u v a c i i' - crossGFamThree_BDiffNormalForm u v a c i i'
        + crossGFamFour_BDiffNormalForm u v a c i i' := by
  have hppu : u ^ (i + i' + 1) = u ^ i * u ^ i' * u := by
    rw [pow_succ, pow_add]
  have hppv : v ^ (i + i' + 1) = v ^ i * v ^ i' * v := by
    rw [pow_succ, pow_add]
  have hpau : u ^ (a + c) = u ^ a * u ^ c := pow_add u a c
  have hpav : v ^ (a + c) = v ^ a * v ^ c := pow_add v a c
  have hua : u ^ a ≠ 0 := pow_ne_zero _ hu0
  have huc : u ^ c ≠ 0 := pow_ne_zero _ hu0
  have hui : u ^ i ≠ 0 := pow_ne_zero _ hu0
  have hui' : u ^ i' ≠ 0 := pow_ne_zero _ hu0
  have hva : v ^ a ≠ 0 := pow_ne_zero _ hv0
  have hvc : v ^ c ≠ 0 := pow_ne_zero _ hv0
  have hvi : v ^ i ≠ 0 := pow_ne_zero _ hv0
  have hvi' : v ^ i' ≠ 0 := pow_ne_zero _ hv0
  simp only [crossGFamOne_BDiffNormalForm, crossGFamTwo_BDiffNormalForm, crossGFamThree_BDiffNormalForm, crossGFamFour_BDiffNormalForm, hppu, hppv, hpau, hpav,
    mul_pow, inv_pow, mul_inv]
  field_simp
  ring

private theorem crossGFam_pair_one_BDiffNormalForm (hu0 : u ≠ 0) (hv0 : v ≠ 0) {a c i i' : ℕ}
    (hi : i < a) (hi' : i' < c) :
    crossGFamOne_BDiffNormalForm u v a c i i' + crossGFamFour_BDiffNormalForm u v a c (a - 1 - i) (c - 1 - i')
      = Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - a - c) := by
  have hup : u ^ (i + i' + 1) ≠ 0 := pow_ne_zero _ hu0
  have hvp : v ^ (i + i' + 1) ≠ 0 := pow_ne_zero _ hv0
  have hua : u ^ (a + c) ≠ 0 := pow_ne_zero _ hu0
  have hva : v ^ (a + c) ≠ 0 := pow_ne_zero _ hv0
  have hum_eq : u ^ ((a - 1 - i) + (c - 1 - i') + 1)
      = u ^ (a + c) * (u ^ (i + i' + 1))⁻¹ := by
    have h : u ^ ((a - 1 - i) + (c - 1 - i') + 1) * u ^ (i + i' + 1) = u ^ (a + c) := by
      rw [← pow_add]
      congr 1
      omega
    field_simp
    linear_combination h
  have hvm_eq : v ^ ((a - 1 - i) + (c - 1 - i') + 1)
      = v ^ (a + c) * (v ^ (i + i' + 1))⁻¹ := by
    have h : v ^ ((a - 1 - i) + (c - 1 - i') + 1) * v ^ (i + i' + 1) = v ^ (a + c) := by
      rw [← pow_add]
      congr 1
      omega
    field_simp
    linear_combination h

  have hGu : Gz u ((i : ℤ) + i' + 1) = u ^ (i + i' + 1) - (u ^ (i + i' + 1))⁻¹ := by
    have hcast : ((i : ℤ) + i' + 1) = ((i + i' + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Gz_natCast, inv_pow]
  have hGv : Gz v ((i : ℤ) + i' + 1 - a - c)
      = v ^ (i + i' + 1) * (v ^ (a + c))⁻¹ - v ^ (a + c) * (v ^ (i + i' + 1))⁻¹ := by
    have h1 : ((i : ℤ) + i' + 1 - a - c) = ((i + i' + 1 : ℕ) : ℤ) - ((a + c : ℕ) : ℤ) := by
      push_cast; ring
    have h2 : -(((i + i' + 1 : ℕ) : ℤ) - ((a + c : ℕ) : ℤ))
        = ((a + c : ℕ) : ℤ) - ((i + i' + 1 : ℕ) : ℤ) := by ring
    simp only [Gz]
    rw [h1, h2, zpow_sub₀ hv0, zpow_sub₀ hv0]
    simp only [zpow_natCast]
    ring
  rw [hGu, hGv]
  simp only [crossGFamOne_BDiffNormalForm, crossGFamFour_BDiffNormalForm, hum_eq, hvm_eq]
  field_simp
  ring

private theorem crossGFam_pair_two_BDiffNormalForm (hu0 : u ≠ 0) (hv0 : v ≠ 0) {a c i i' : ℕ}
    (hi : i < a) (hi' : i' < c) :
    crossGFamTwo_BDiffNormalForm u v a c i i' + crossGFamThree_BDiffNormalForm u v a c (a - 1 - i) (c - 1 - i')
      = Gz u ((i : ℤ) + i' + 1 - c) * Gz v ((i : ℤ) + i' + 1 - a) := by
  have hup : u ^ (i + i' + 1) ≠ 0 := pow_ne_zero _ hu0
  have hvp : v ^ (i + i' + 1) ≠ 0 := pow_ne_zero _ hv0
  have hua : u ^ a ≠ 0 := pow_ne_zero _ hu0
  have huc : u ^ c ≠ 0 := pow_ne_zero _ hu0
  have hva : v ^ a ≠ 0 := pow_ne_zero _ hv0
  have hvc : v ^ c ≠ 0 := pow_ne_zero _ hv0
  have hum : u ^ ((a - 1 - i) + (c - 1 - i') + 1) ≠ 0 := pow_ne_zero _ hu0
  have hvm : v ^ ((a - 1 - i) + (c - 1 - i') + 1) ≠ 0 := pow_ne_zero _ hv0

  have hGu : Gz u ((i : ℤ) + i' + 1 - c)
      = u ^ (i + i' + 1) * (u ^ c)⁻¹ - u ^ c * (u ^ (i + i' + 1))⁻¹ := by
    have h1 : ((i : ℤ) + i' + 1 - c) = ((i + i' + 1 : ℕ) : ℤ) - (c : ℤ) := by push_cast; ring
    have h2 : -(((i + i' + 1 : ℕ) : ℤ) - (c : ℤ)) = (c : ℤ) - ((i + i' + 1 : ℕ) : ℤ) := by ring
    simp only [Gz]
    rw [h1, h2, zpow_sub₀ hu0, zpow_sub₀ hu0]
    simp only [zpow_natCast]
    ring
  have hGv : Gz v ((i : ℤ) + i' + 1 - a)
      = v ^ (i + i' + 1) * (v ^ a)⁻¹ - v ^ a * (v ^ (i + i' + 1))⁻¹ := by
    have h1 : ((i : ℤ) + i' + 1 - a) = ((i + i' + 1 : ℕ) : ℤ) - (a : ℤ) := by push_cast; ring
    have h2 : -(((i + i' + 1 : ℕ) : ℤ) - (a : ℤ)) = (a : ℤ) - ((i + i' + 1 : ℕ) : ℤ) := by ring
    simp only [Gz]
    rw [h1, h2, zpow_sub₀ hv0, zpow_sub₀ hv0]
    simp only [zpow_natCast]
    ring
  rw [hGu, hGv]

  have hm : ((a - 1 - i) + (c - 1 - i') + 1) + (i + i' + 1) = a + c := by omega
  have hupow : u ^ ((a - 1 - i) + (c - 1 - i') + 1) * u ^ (i + i' + 1) = u ^ a * u ^ c := by
    rw [← pow_add, ← pow_add, hm]
  have hvpow : v ^ ((a - 1 - i) + (c - 1 - i') + 1) * v ^ (i + i' + 1) = v ^ a * v ^ c := by
    rw [← pow_add, ← pow_add, hm]
  have hum_eq : u ^ ((a - 1 - i) + (c - 1 - i') + 1)
      = u ^ a * u ^ c * (u ^ (i + i' + 1))⁻¹ := by
    field_simp
    linear_combination hupow
  have hvm_eq : v ^ ((a - 1 - i) + (c - 1 - i') + 1)
      = v ^ a * v ^ c * (v ^ (i + i' + 1))⁻¹ := by
    field_simp
    linear_combination hvpow
  simp only [crossGFamTwo_BDiffNormalForm, crossGFamThree_BDiffNormalForm]
  rw [hum_eq, hvm_eq]
  field_simp
  ring

private theorem crossGPair_side_distrib_BDiffNormalForm (P w : K) (a c : ℕ) :
    P * (w * (∑ i ∈ Finset.range a, w ^ i) * (∑ i ∈ Finset.range c, w ^ i)
        * (w ^ a)⁻¹ * (w ^ c)⁻¹)
      = ∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c,
          P * (w * (w ^ a)⁻¹ * (w ^ c)⁻¹) * (w ^ i * w ^ i') := by
  rw [show P * (w * (∑ i ∈ Finset.range a, w ^ i) * (∑ i ∈ Finset.range c, w ^ i)
        * (w ^ a)⁻¹ * (w ^ c)⁻¹)
      = ((∑ i ∈ Finset.range a, w ^ i) * (∑ i ∈ Finset.range c, w ^ i))
          * (P * (w * (w ^ a)⁻¹ * (w ^ c)⁻¹)) by ring,
    Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  ring

private theorem crossGPair_perterm_BDiffNormalForm (hu0 : u ≠ 0) (hv0 : v ≠ 0) {a c i i' : ℕ}
    (hi : i < a) (hi' : i' < c) :
    (u ^ a - v ^ a) * (u ^ c - v ^ c)
        * (u * v * ((u * v) ^ a)⁻¹ * ((u * v) ^ c)⁻¹) * ((u * v) ^ i * (u * v) ^ i')
      - (u ^ a - (v ^ a)⁻¹) * (u ^ c - (v ^ c)⁻¹)
          * (u * v⁻¹ * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ c)⁻¹)
          * ((u * v⁻¹) ^ i * (u * v⁻¹) ^ i')
    = (Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - a - c)
        - Gz u ((i : ℤ) + i' + 1 - c) * Gz v ((i : ℤ) + i' + 1 - a))
      + (crossGFamFour_BDiffNormalForm u v a c i i' - crossGFamFour_BDiffNormalForm u v a c (a - 1 - i) (c - 1 - i'))
      - (crossGFamThree_BDiffNormalForm u v a c i i' - crossGFamThree_BDiffNormalForm u v a c (a - 1 - i) (c - 1 - i')) := by
  rw [crossGPair_summand_BDiffNormalForm hu0 hv0 a c i i', ← crossGFam_pair_one_BDiffNormalForm hu0 hv0 hi hi',
    ← crossGFam_pair_two_BDiffNormalForm hu0 hv0 hi hi']
  ring

private theorem crossGFamFour_reflect_BDiffNormalForm (a c : ℕ) :
    (∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c,
        crossGFamFour_BDiffNormalForm u v a c (a - 1 - i) (c - 1 - i'))
      = ∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c, crossGFamFour_BDiffNormalForm u v a c i i' := by
  rw [← Finset.sum_range_reflect
    (fun i => ∑ i' ∈ Finset.range c, crossGFamFour_BDiffNormalForm u v a c i i') a]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_range_reflect (fun i' => crossGFamFour_BDiffNormalForm u v a c (a - 1 - i) i') c

private theorem crossGFamThree_reflect_BDiffNormalForm (a c : ℕ) :
    (∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c,
        crossGFamThree_BDiffNormalForm u v a c (a - 1 - i) (c - 1 - i'))
      = ∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c, crossGFamThree_BDiffNormalForm u v a c i i' := by
  rw [← Finset.sum_range_reflect
    (fun i => ∑ i' ∈ Finset.range c, crossGFamThree_BDiffNormalForm u v a c i i') a]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_range_reflect (fun i' => crossGFamThree_BDiffNormalForm u v a c (a - 1 - i) i') c

theorem crossPairG_expansion (hu0 : u ≠ 0) (hv0 : v ≠ 0) (a c : ℕ) :
    (u ^ a - v ^ a) * (u ^ c - v ^ c)
        * (u * v * (∑ i ∈ Finset.range a, (u * v) ^ i) * (∑ i ∈ Finset.range c, (u * v) ^ i)
            * ((u * v) ^ a)⁻¹ * ((u * v) ^ c)⁻¹)
      - (u ^ a - (v ^ a)⁻¹) * (u ^ c - (v ^ c)⁻¹)
          * (u * v⁻¹ * (∑ i ∈ Finset.range a, (u * v⁻¹) ^ i)
              * (∑ i ∈ Finset.range c, (u * v⁻¹) ^ i)
              * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ c)⁻¹)
    = ∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c,
        (Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - a - c)
          - Gz u ((i : ℤ) + i' + 1 - c) * Gz v ((i : ℤ) + i' + 1 - a)) := by

  have hdist : (u ^ a - v ^ a) * (u ^ c - v ^ c)
        * (u * v * (∑ i ∈ Finset.range a, (u * v) ^ i) * (∑ i ∈ Finset.range c, (u * v) ^ i)
            * ((u * v) ^ a)⁻¹ * ((u * v) ^ c)⁻¹)
      - (u ^ a - (v ^ a)⁻¹) * (u ^ c - (v ^ c)⁻¹)
          * (u * v⁻¹ * (∑ i ∈ Finset.range a, (u * v⁻¹) ^ i)
              * (∑ i ∈ Finset.range c, (u * v⁻¹) ^ i)
              * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ c)⁻¹)
      = ∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c,
          ((u ^ a - v ^ a) * (u ^ c - v ^ c)
              * (u * v * ((u * v) ^ a)⁻¹ * ((u * v) ^ c)⁻¹) * ((u * v) ^ i * (u * v) ^ i')
            - (u ^ a - (v ^ a)⁻¹) * (u ^ c - (v ^ c)⁻¹)
                * (u * v⁻¹ * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ c)⁻¹)
                * ((u * v⁻¹) ^ i * (u * v⁻¹) ^ i')) := by
    rw [crossGPair_side_distrib_BDiffNormalForm ((u ^ a - v ^ a) * (u ^ c - v ^ c)) (u * v) a c,
      crossGPair_side_distrib_BDiffNormalForm ((u ^ a - (v ^ a)⁻¹) * (u ^ c - (v ^ c)⁻¹)) (u * v⁻¹) a c,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_sub_distrib _ _).symm
  rw [hdist]

  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun i' hi' =>
    crossGPair_perterm_BDiffNormalForm hu0 hv0 (Finset.mem_range.mp hi) (Finset.mem_range.mp hi')]

  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [crossGFamFour_reflect_BDiffNormalForm, crossGFamThree_reflect_BDiffNormalForm]
  ring

theorem xfun_sub_mul_Fz_sub_mul_Fz_sub_expansion (hu : u ≠ 0) (hv : v ≠ 0)
    (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (a c : ℕ) :
    (xfun (u * v) - xfun (u * v⁻¹))
        * ((Fz u (a : ℤ) - Fz v (a : ℤ)) * (Fz u (c : ℤ) - Fz v (c : ℤ)))
      = ∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c,
          (Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - a - c)
            - Gz u ((i : ℤ) + i' + 1 - c) * Gz v ((i : ℤ) + i' + 1 - a)) := by
  rw [xfun_sub_mul_Fz_sub_mul_Fz_sub hu hv huvm huvd a c]
  exact crossPairG_expansion hu hv a c

end CrossPairGExpansion
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section AbsorbedNormalForm

theorem psiCoeffFull_pos_eq_divisorSum_Gz (w : K) {N : ℕ} (hN : 0 < N) :
    psiCoeffFull w N = ∑ d ∈ N.divisors, (d : K) ^ 2 * Gz w (d : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact psiCoeffFull_succ_eq_divisorSum_Gz m

theorem xCoeffFull_sub_eq_divisorSum (u v : K) {n : ℕ} (hn : 0 < n) :
    xCoeffFull u n - xCoeffFull v n
      = ∑ d ∈ n.divisors, (d : K) * (Fz u (d : ℤ) - Fz v (d : ℤ)) := by
  rw [xCoeffFull_of_pos u hn, xCoeffFull_of_pos v hn, xCoeff, xCoeff,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun d _ => by
    rw [xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz]; ring

theorem cauchyMulInt_diff_eq_divisorSum (u v : K) (N : ℕ) :
    cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
        (fun i => xCoeffFull u i - xCoeffFull v i) N
      = ∑ b ∈ Finset.Ico 1 N, ∑ d ∈ b.divisors, ∑ e ∈ (N - b).divisors,
          ((d : K) * (Fz u (d : ℤ) - Fz v (d : ℤ)))
            * ((e : K) * (Fz u (e : ℤ) - Fz v (e : ℤ))) := by
  simp only [cauchyMulInt]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_Ico] at hb
  have hb1 : 0 < b := hb.1
  have hb2 : 0 < N - b := by omega
  rw [xCoeffFull_sub_eq_divisorSum u v hb1, xCoeffFull_sub_eq_divisorSum u v hb2,
    Finset.sum_mul_sum]

theorem cauchyMulInt_psiCoeffFull_eq_rows (u v : K) (M : ℕ) :
    cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M
      = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ e ∈ (M - i).divisors,
          (d : K) ^ 2 * (e : K) ^ 2 * (Gz u (d : ℤ) * Gz v (e : ℤ)) := by
  simp only [cauchyMulInt]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  have hi1 : 0 < i := hi.1
  have hi2 : 0 < M - i := by omega
  rw [psiCoeffFull_pos_eq_divisorSum_Gz u hi1, psiCoeffFull_pos_eq_divisorSum_Gz v hi2,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => by ring

theorem xfun_sub_mul_cauchyMulInt_diff_eq_crossRows (hu : u ≠ 0) (hv : v ≠ 0)
    (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (M : ℕ) :
    (xfun (u * v) - xfun (u * v⁻¹))
        * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
            (fun i => xCoeffFull u i - xCoeffFull v i) M
      = ∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ e ∈ (M - b).divisors,
          (d : K) * (e : K)
            * ∑ i ∈ Finset.range d, ∑ i' ∈ Finset.range e,
                (Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - d - e)
                  - Gz u ((i : ℤ) + i' + 1 - e) * Gz v ((i : ℤ) + i' + 1 - d)) := by
  rw [cauchyMulInt_diff_eq_divisorSum u v M, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show (xfun (u * v) - xfun (u * v⁻¹))
        * ((d : K) * (Fz u (d : ℤ) - Fz v (d : ℤ))
            * ((e : K) * (Fz u (e : ℤ) - Fz v (e : ℤ))))
      = (d : K) * (e : K)
          * ((xfun (u * v) - xfun (u * v⁻¹))
              * ((Fz u (d : ℤ) - Fz v (d : ℤ)) * (Fz u (e : ℤ) - Fz v (e : ℤ)))) by ring,
    xfun_sub_mul_Fz_sub_mul_Fz_sub_expansion hu hv huvm huvd d e]

theorem addDefectDiffCoeff_eq_absorbed (hu : u ≠ 0) (hv : v ≠ 0)
    (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M) :
    addDefectDiffCoeff u v M
      = (∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ e ∈ (M - b).divisors,
            (d : K) * (e : K)
              * ∑ i ∈ Finset.range d, ∑ i' ∈ Finset.range e,
                  (Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - d - e)
                    - Gz u ((i : ℤ) + i' + 1 - e) * Gz v ((i : ℤ) + i' + 1 - d)))
        + (∑ b ∈ Finset.Ico 1 M,
              (∑ d ∈ b.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
                * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                    (fun i => xCoeffFull u i - xCoeffFull v i) (M - b))
        + cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M
        + svComplex u v M := by
  have hsplit := addDefectDiffCoeff_eq_boundary_add_int u v hM
  have hcross := xfun_sub_mul_cauchyMulInt_diff_eq_crossRows hu hv huvm huvd M

  have h4 : (∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a - xCoeff (u * v⁻¹) a)
        * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a)))
            + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)))
      = (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
            * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a)))))
        + ∑ b ∈ Finset.Ico 1 M,
            (∑ d ∈ b.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
              * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                  (fun i => xCoeffFull u i - xCoeffFull v i) (M - b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [xCoeff_mul_sub_xCoeff_mul_inv hu hv a]
    ring

  have h3 := xCoeff_mul_sub_xCoeff_mul_inv hu hv M
  simp only [svComplex]
  linear_combination hsplit + hcross + h4 + (xfun u - xfun v) ^ 2 * h3

end AbsorbedNormalForm
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt cauchyMul_eq_boundary_add_int cauchyMul_cube_eq_boundary_add_int xCoeffFull_of_pos cauchyMulInt_xx_eq_sum_Sols defectCoeff_eq_boundary_add_int Fz Gz Fz_zero Gz_zero Fz_neg Gz_neg Fz_natCast Gz_natCast Fz_mul_Fz Fz_mul_Gz xDivTerm_eq_mul_Fz tent xfun_mul_Fz_eq_tent tent_eq_sq_add_sum_Ico cauchyMul cauchyMul_zero xCoeffFull xCoeffFull_zero a₄Coeff a₄Coeff_zero a₆Coeff xfun yfun pointX pointY term b a₄ curve xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff psifun svComplex LatticeRep OnHalfLattice ks17_A_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section SameVarReduction

theorem xfun_sq_mul_Gz_one (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    xfun u ^ 2 * Gz u 1 = -psifun u := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  simp only [psifun, xfun, yfun, Gz, zpow_one, zpow_neg]
  field_simp
  ring

theorem xfun_mul_Gz_sub_nsmul_Gz_one (hu0 : u ≠ 0) (hu1 : u ≠ 1) (d : ℕ) :
    xfun u * (Gz u (d : ℤ) - (d : K) * Gz u 1)
      = Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
      · simp [Gz]
      · simp
    · obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
      have IH := ih m (by omega)
      have hFG := Fz_mul_Gz hu0 ((m + 1 : ℕ) : ℤ) 1
      have htent := xfun_mul_Fz_eq_tent hu0 hu1 (m + 1)
      have e1 : ((m + 1 : ℕ) : ℤ) + 1 = ((m + 2 : ℕ) : ℤ) := by push_cast; ring
      have e2 : ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2] at hFG
      have hsplit : ∑ j ∈ Finset.range ((m + 2) / 2), tent u (m + 2 - 1 - 2 * j)
          = (∑ j ∈ Finset.range (m / 2), tent u (m - 1 - 2 * j)) + tent u (m + 1) := by
        have h2 : (m + 2) / 2 = m / 2 + 1 := by omega
        rw [h2, Finset.sum_range_succ']

        congr 1
        exact Finset.sum_congr rfl fun j _ => by congr 1; omega
      rw [hsplit]
      have hcast : ((m + 2 : ℕ) : K) = ((m : ℕ) : K) + 2 := by push_cast; ring
      rw [hcast]
      linear_combination IH + Gz u 1 * htent - xfun u * hFG

theorem xfun_sq_mul_Gz_add_psifun (hu0 : u ≠ 0) (hu1 : u ≠ 1) (d : ℕ) :
    xfun u ^ 2 * Gz u (d : ℤ) + (d : K) * psifun u
      = (xfun u * Gz u 1) * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j) := by
  have hN1 := xfun_sq_mul_Gz_one hu0 hu1
  have hN2 := xfun_mul_Gz_sub_nsmul_Gz_one hu0 hu1 d
  linear_combination (d : K) * hN1 + xfun u * hN2

end SameVarReduction
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section CrossInteriorFlattening

theorem Fz_mul_Fz_mul_Gz (hu : u ≠ 0) (a b c : ℤ) :
    Fz u a * Fz u b * Gz u c
      = Gz u (a + b + c) - Gz u (a + b - c) + Gz u (a - b + c) - Gz u (a - b - c)
        - 2 * Gz u (a + c) + 2 * Gz u (a - c) - 2 * Gz u (b + c) + 2 * Gz u (b - c)
        + 4 * Gz u c := by
  have h5 := Fz_mul_Fz hu a b
  have h1 := Fz_mul_Gz hu (a + b) c
  have h2 := Fz_mul_Gz hu (a - b) c
  have h3 := Fz_mul_Gz hu a c
  have h4 := Fz_mul_Gz hu b c
  linear_combination Gz u c * h5 + h1 + h2 - 2 * h3 - 2 * h4

theorem Gz_mul_Gz_mul_Fz_sub_mul_Fz_sub (hu : u ≠ 0) (hv : v ≠ 0) (d e f : ℤ) :
    Gz u d * Gz v d * ((Fz u e - Fz v e) * (Fz u f - Fz v f))
      = (Gz u (e + f + d) - Gz u (e + f - d) + Gz u (e - f + d) - Gz u (e - f - d)
            - 2 * Gz u (e + d) + 2 * Gz u (e - d) - 2 * Gz u (f + d) + 2 * Gz u (f - d)
            + 4 * Gz u d) * Gz v d
        - (Gz u (e + d) - Gz u (e - d) - 2 * Gz u d)
            * (Gz v (f + d) - Gz v (f - d) - 2 * Gz v d)
        - (Gz u (f + d) - Gz u (f - d) - 2 * Gz u d)
            * (Gz v (e + d) - Gz v (e - d) - 2 * Gz v d)
        + Gz u d * (Gz v (e + f + d) - Gz v (e + f - d) + Gz v (e - f + d) - Gz v (e - f - d)
            - 2 * Gz v (e + d) + 2 * Gz v (e - d) - 2 * Gz v (f + d) + 2 * Gz v (f - d)
            + 4 * Gz v d) := by
  have hu1 := Fz_mul_Fz_mul_Gz hu e f d
  have hv1 := Fz_mul_Fz_mul_Gz hv e f d
  have hue := Fz_mul_Gz hu e d
  have huf := Fz_mul_Gz hu f d
  have hve := Fz_mul_Gz hv e d
  have hvf := Fz_mul_Gz hv f d
  linear_combination Gz v d * hu1 + Gz u d * hv1
    - (Fz v f * Gz v d) * hue - (Gz u (e + d) - Gz u (e - d) - 2 * Gz u d) * hvf
    - (Fz v e * Gz v d) * huf - (Gz u (f + d) - Gz u (f - d) - 2 * Gz u d) * hve

theorem crossInterior_block_eq_rows (hu : u ≠ 0) (hv : v ≠ 0) (M : ℕ) :
    ∑ b ∈ Finset.Ico 1 M, (∑ d ∈ b.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
        * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
            (fun i => xCoeffFull u i - xCoeffFull v i) (M - b)
      = ∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ c ∈ Finset.Ico 1 (M - b),
          ∑ e ∈ c.divisors, ∑ f ∈ (M - b - c).divisors,
            (d : K) * (e : K) * (f : K)
              * ((Gz u ((e : ℤ) + f + d) - Gz u ((e : ℤ) + f - d) + Gz u ((e : ℤ) - f + d)
                    - Gz u ((e : ℤ) - f - d) - 2 * Gz u ((e : ℤ) + d) + 2 * Gz u ((e : ℤ) - d)
                    - 2 * Gz u ((f : ℤ) + d) + 2 * Gz u ((f : ℤ) - d)
                    + 4 * Gz u (d : ℤ)) * Gz v (d : ℤ)
                - (Gz u ((e : ℤ) + d) - Gz u ((e : ℤ) - d) - 2 * Gz u (d : ℤ))
                    * (Gz v ((f : ℤ) + d) - Gz v ((f : ℤ) - d) - 2 * Gz v (d : ℤ))
                - (Gz u ((f : ℤ) + d) - Gz u ((f : ℤ) - d) - 2 * Gz u (d : ℤ))
                    * (Gz v ((e : ℤ) + d) - Gz v ((e : ℤ) - d) - 2 * Gz v (d : ℤ))
                + Gz u (d : ℤ) * (Gz v ((e : ℤ) + f + d) - Gz v ((e : ℤ) + f - d)
                    + Gz v ((e : ℤ) - f + d) - Gz v ((e : ℤ) - f - d) - 2 * Gz v ((e : ℤ) + d)
                    + 2 * Gz v ((e : ℤ) - d) - 2 * Gz v ((f : ℤ) + d) + 2 * Gz v ((f : ℤ) - d)
                    + 4 * Gz v (d : ℤ))) := by
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cauchyMulInt_diff_eq_divisorSum u v (M - b), Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h := Gz_mul_Gz_mul_Fz_sub_mul_Fz_sub hu hv (d : ℤ) (e : ℤ) (f : ℤ)
  linear_combination ((d : K) * (e : K) * (f : K)) * h

end CrossInteriorFlattening
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt cauchyMul_eq_boundary_add_int cauchyMul_cube_eq_boundary_add_int xCoeffFull_of_pos cauchyMulInt_xx_eq_sum_Sols defectCoeff_eq_boundary_add_int Fz Gz Fz_zero Gz_zero Fz_neg Gz_neg Fz_natCast Gz_natCast Fz_mul_Fz Fz_mul_Gz xDivTerm_eq_mul_Fz tent xfun_mul_Fz_eq_tent tent_eq_sq_add_sum_Ico cauchyMul cauchyMul_zero xCoeffFull xCoeffFull_zero a₄Coeff a₄Coeff_zero a₆Coeff xfun yfun pointX pointY term b a₄ curve xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff psifun svComplex LatticeRep OnHalfLattice ks17_A_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section CarrierToolkit

theorem xfun_mul_Gz_split (hu0 : u ≠ 0) (hu1 : u ≠ 1) (e : ℕ) :
    xfun u * Gz u (e : ℤ)
      = (e : K) * (xfun u * Gz u 1)
        + Gz u 1 * ∑ j ∈ Finset.range (e / 2), tent u (e - 1 - 2 * j) := by
  linear_combination xfun_mul_Gz_sub_nsmul_Gz_one hu0 hu1 e

theorem Gz_one_mul_tent [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (k : ℕ) :
    Gz u 1 * tent u k
      = (k : K) ^ 2 * Gz u 1
        + ∑ j ∈ Finset.Ico 1 k,
            ((k - j : ℕ) : K) * (Gz u ((j : ℤ) + 1) - Gz u ((j : ℤ) - 1) - 2 * Gz u 1) := by
  rw [tent_eq_sq_add_sum_Ico hu0 hu1 k, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    have h := Fz_mul_Gz hu0 (j : ℤ) 1
    linear_combination ((k - j : ℕ) : K) * h

theorem xfunG1_mul_tent [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (k : ℕ) :
    (xfun u * Gz u 1) * tent u k
      = (k : K) ^ 2 * (xfun u * Gz u 1)
        + ∑ m ∈ Finset.Ico 1 k, ((k - m : ℕ) : K) * (Gz u 1 * tent u m) := by
  rw [tent_eq_sq_add_sum_Ico hu0 hu1 k, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun m _ => ?_
    have h := xfun_mul_Fz_eq_tent hu0 hu1 m
    linear_combination ((k - m : ℕ) : K) * Gz u 1 * h

end CarrierToolkit
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section CheckpointBlocks

theorem xCoeff_sub_xCoeff_eq_divisorSum (u v : K) (n : ℕ) :
    xCoeff u n - xCoeff v n
      = ∑ f ∈ n.divisors, (f : K) * (Fz u (f : ℤ) - Fz v (f : ℤ)) := by
  rw [xCoeff, xCoeff, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun f _ => by
    rw [xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz]; ring

theorem two_mul_xfun_sub_mul_xCoeff_sub (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) (n : ℕ) :
    2 * ((xfun u - xfun v) * (xCoeff u n - xCoeff v n))
      = 2 * ∑ f ∈ n.divisors, (f : K) * (tent u f + tent v f)
        - 2 * (xfun u * xCoeff v n + xfun v * xCoeff u n) := by
  have hxu : (∑ f ∈ n.divisors, (f : K) * Fz u (f : ℤ)) = xCoeff u n :=
    Finset.sum_congr rfl fun f _ => (xDivTerm_eq_mul_Fz u f).symm
  have hxv : (∑ f ∈ n.divisors, (f : K) * Fz v (f : ℤ)) = xCoeff v n :=
    Finset.sum_congr rfl fun f _ => (xDivTerm_eq_mul_Fz v f).symm
  have h1 : ∑ f ∈ n.divisors, (2 * xfun u) * ((f : K) * Fz v (f : ℤ))
      = (2 * xfun u) * xCoeff v n := by rw [← Finset.mul_sum, hxv]
  have h2 : ∑ f ∈ n.divisors, (2 * xfun v) * ((f : K) * Fz u (f : ℤ))
      = (2 * xfun v) * xCoeff u n := by rw [← Finset.mul_sum, hxu]
  have h3 : ∑ f ∈ n.divisors, 2 * ((f : K) * (tent u f + tent v f))
      = 2 * ∑ f ∈ n.divisors, (f : K) * (tent u f + tent v f) := by rw [Finset.mul_sum]
  have hkey : ∀ f ∈ n.divisors,
      2 * ((xfun u - xfun v) * ((f : K) * (Fz u (f : ℤ) - Fz v (f : ℤ))))
        = 2 * ((f : K) * (tent u f + tent v f))
          - (2 * xfun u) * ((f : K) * Fz v (f : ℤ))
          - (2 * xfun v) * ((f : K) * Fz u (f : ℤ)) := by
    intro f _
    have htu := xfun_mul_Fz_eq_tent hu0 hu1 f
    have htv := xfun_mul_Fz_eq_tent hv0 hv1 f
    linear_combination (2 * (f : K)) * htu + (2 * (f : K)) * htv
  have hstep : 2 * ((xfun u - xfun v) * (xCoeff u n - xCoeff v n))
      = ∑ f ∈ n.divisors,
          (2 * ((f : K) * (tent u f + tent v f))
            - (2 * xfun u) * ((f : K) * Fz v (f : ℤ))
            - (2 * xfun v) * ((f : K) * Fz u (f : ℤ))) := by
    rw [xCoeff_sub_xCoeff_eq_divisorSum u v n, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hkey
  rw [hstep, Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1, h2, h3]
  ring

theorem orderThree_pairing (hu0 : u ≠ 0) (hu1 : u ≠ 1) (v : K) {M : ℕ} (hM : 0 < M) :
    (∑ d ∈ M.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * xfun u ^ 2
        + psifun u * psiCoeffFull v M
      = ∑ d ∈ M.divisors,
          (d : K) * (Gz v (d : ℤ)
            * ((xfun u * Gz u 1) * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))) := by
  rw [psiCoeffFull_pos_eq_divisorSum_Gz v hM, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h := xfun_sq_mul_Gz_add_psifun hu0 hu1 d
  linear_combination ((d : K) * Gz v (d : ℤ)) * h

end CheckpointBlocks
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section SimplePoleCheckpoint

theorem svComplex_eq_simplePoleForm (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    {M : ℕ} (hM : 0 < M) :
    svComplex u v M
      = 2 * ((xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M)))
        - 2 * (xfun u * xfun v) * (∑ d ∈ M.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
        + (∑ d ∈ M.divisors, (d : K)
            * (Gz v (d : ℤ)
                * ((xfun u * Gz u 1) * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
              + Gz u (d : ℤ)
                * ((xfun v * Gz v 1) * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))))
        + (∑ a ∈ Finset.Ico 1 M,
            (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
              * (2 * ∑ f ∈ (M - a).divisors, (f : K) * (tent u f + tent v f)))
        - ∑ a ∈ Finset.Ico 1 M,
            (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
              * (2 * (xfun u * xCoeff v (M - a) + xfun v * xCoeff u (M - a))) := by

  have hB4 : (∑ a ∈ Finset.Ico 1 M,
        (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
          * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a)))))
      = (∑ a ∈ Finset.Ico 1 M,
            (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
              * (2 * ∑ f ∈ (M - a).divisors, (f : K) * (tent u f + tent v f)))
        - ∑ a ∈ Finset.Ico 1 M,
            (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
              * (2 * (xfun u * xCoeff v (M - a) + xfun v * xCoeff u (M - a))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [two_mul_xfun_sub_mul_xCoeff_sub hu0 hu1 hv0 hv1 (M - a)]
    ring

  have hOu := orderThree_pairing hu0 hu1 v hM
  have hOv := orderThree_pairing hv0 hv1 u hM

  have hOv' : (∑ d ∈ M.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * xfun v ^ 2
        + psiCoeffFull u M * psifun v
      = ∑ d ∈ M.divisors,
          (d : K) * (Gz u (d : ℤ)
            * ((xfun v * Gz v 1) * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))) := by
    have hswap : (∑ d ∈ M.divisors, (d : K) * (Gz v (d : ℤ) * Gz u (d : ℤ)))
        = ∑ d ∈ M.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)) :=
      Finset.sum_congr rfl fun d _ => by ring
    calc (∑ d ∈ M.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * xfun v ^ 2
          + psiCoeffFull u M * psifun v
        = (∑ d ∈ M.divisors, (d : K) * (Gz v (d : ℤ) * Gz u (d : ℤ))) * xfun v ^ 2
            + psifun v * psiCoeffFull u M := by rw [hswap]; ring
      _ = ∑ d ∈ M.divisors,
            (d : K) * (Gz u (d : ℤ)
              * ((xfun v * Gz v 1) * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))) :=
          hOv

  have hsplit : (∑ d ∈ M.divisors, (d : K)
        * (Gz v (d : ℤ)
            * ((xfun u * Gz u 1) * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
          + Gz u (d : ℤ)
            * ((xfun v * Gz v 1) * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))))
      = (∑ d ∈ M.divisors,
          (d : K) * (Gz v (d : ℤ)
            * ((xfun u * Gz u 1) * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))))
        + ∑ d ∈ M.divisors,
          (d : K) * (Gz u (d : ℤ)
            * ((xfun v * Gz v 1) * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring

  simp only [svComplex]
  rw [hsplit]
  linear_combination hB4 + hOu + hOv'

end SimplePoleCheckpoint
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt cauchyMul_eq_boundary_add_int cauchyMul_cube_eq_boundary_add_int xCoeffFull_of_pos cauchyMulInt_xx_eq_sum_Sols defectCoeff_eq_boundary_add_int Fz Gz Fz_zero Gz_zero Fz_neg Gz_neg Fz_natCast Gz_natCast Fz_mul_Fz Fz_mul_Gz xDivTerm_eq_mul_Fz tent xfun_mul_Fz_eq_tent tent_eq_sq_add_sum_Ico cauchyMul cauchyMul_zero xCoeffFull xCoeffFull_zero a₄Coeff a₄Coeff_zero a₆Coeff xfun yfun pointX pointY term b a₄ curve xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff psifun svComplex LatticeRep OnHalfLattice ks17_A_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section Collection

theorem Gz_one_mul_tent_eq_sum (w : K) (hw0 : w ≠ 0) (e : ℕ) :
    Gz w 1 * tent w e = 2 * ∑ j ∈ Finset.Ico 1 e, Gz w (j : ℤ) + Gz w (e : ℤ) := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  have hwe : (w : K) ^ e ≠ 0 := pow_ne_zero _ hw0
  have hg : (∑ i ∈ Finset.range e, w ^ i) * (w - 1) = w ^ e - 1 := geom_sum_mul w e

  have hrev : ∑ i ∈ Finset.range e, w⁻¹ ^ i
      = w * (w ^ e)⁻¹ * ∑ i ∈ Finset.range e, w ^ i := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect (fun i => w * (w ^ e)⁻¹ * w ^ i) e]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hie := Finset.mem_range.mp hi
    have hsplit : (w : K) ^ e = w ^ (e - 1 - i) * w ^ (i + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [inv_pow]
    field_simp
    rw [hsplit]
    ring

  have hIcoP : ∑ j ∈ Finset.Ico 1 e, Gz w (j : ℤ)
      = (∑ i ∈ Finset.range e, w ^ i) - ∑ i ∈ Finset.range e, w⁻¹ ^ i := by
    have h0 : ∑ j ∈ Finset.Ico 1 e, ((w : K) ^ j - w⁻¹ ^ j)
        = ∑ j ∈ Finset.range e, ((w : K) ^ j - w⁻¹ ^ j) := by
      apply Finset.sum_subset
      · intro x hx
        rw [Finset.mem_Ico] at hx
        exact Finset.mem_range.mpr hx.2
      · intro x hx hnx
        have hx0 : x = 0 := by
          rw [Finset.mem_range] at hx
          rw [Finset.mem_Ico] at hnx
          omega
        simp [hx0]
    calc ∑ j ∈ Finset.Ico 1 e, Gz w (j : ℤ)
        = ∑ j ∈ Finset.Ico 1 e, ((w : K) ^ j - w⁻¹ ^ j) :=
          Finset.sum_congr rfl fun j _ => Gz_natCast w j
      _ = ∑ j ∈ Finset.range e, ((w : K) ^ j - w⁻¹ ^ j) := h0
      _ = (∑ i ∈ Finset.range e, w ^ i) - ∑ i ∈ Finset.range e, w⁻¹ ^ i := by
          rw [Finset.sum_sub_distrib]
  have hG1 : Gz w 1 = w - w⁻¹ := by
    simp [Gz, zpow_one]
  rw [hG1, hIcoP, hrev, Gz_natCast, inv_pow]
  simp only [tent]
  field_simp
  linear_combination ((∑ i ∈ Finset.range e, w ^ i) * w + (∑ i ∈ Finset.range e, w ^ i)
      + w ^ e + 1) * hg

theorem sum_succ_mul_Gz_sub_eq_sum (w : K) (e : ℕ) :
    ∑ i ∈ Finset.range e,
        (((i + 1 : ℕ) : K) * Gz w ((e - i : ℕ) : ℤ) - ((e - 1 - i : ℕ) : K) * Gz w (i : ℤ))
      = 2 * ∑ j ∈ Finset.Ico 1 e, Gz w (j : ℤ) + Gz w (e : ℤ) := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp

  have hIco : ∑ i ∈ Finset.range e, Gz w (i : ℤ) = ∑ j ∈ Finset.Ico 1 e, Gz w (j : ℤ) := by
    rw [eq_comm]
    apply Finset.sum_subset
    · intro x hx
      rw [Finset.mem_Ico] at hx
      exact Finset.mem_range.mpr hx.2
    · intro x hx hnx
      have hx0 : x = 0 := by
        rw [Finset.mem_range] at hx
        rw [Finset.mem_Ico] at hnx
        omega
      simp [hx0]

  have hrefl : ∑ i ∈ Finset.range e, ((i + 1 : ℕ) : K) * Gz w ((e - i : ℕ) : ℤ)
      = ∑ i ∈ Finset.range e, ((e - i : ℕ) : K) * Gz w ((i + 1 : ℕ) : ℤ) := by
    rw [← Finset.sum_range_reflect (fun i => ((e - i : ℕ) : K) * Gz w ((i + 1 : ℕ) : ℤ)) e]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hie := Finset.mem_range.mp hi
    have h₁ : e - (e - 1 - i) = i + 1 := by omega
    have h₂ : e - 1 - i + 1 = e - i := by omega
    rw [h₁, h₂]

  have hper : ∀ i ∈ Finset.range e,
      ((e - i : ℕ) : K) * Gz w ((i + 1 : ℕ) : ℤ) - ((e - 1 - i : ℕ) : K) * Gz w (i : ℤ)
        = (((e + 1 - (i + 1) : ℕ) : K) * Gz w ((i + 1 : ℕ) : ℤ)
            - ((e + 1 - i : ℕ) : K) * Gz w (i : ℤ))
          + 2 * Gz w (i : ℤ) := by
    intro i hi
    have hie := Finset.mem_range.mp hi
    have c₁ : (e + 1 - (i + 1) : ℕ) = e - i := by omega
    have c₂ : ((e + 1 - i : ℕ) : K) = ((e - 1 - i : ℕ) : K) + 2 := by
      have h : (e + 1 - i : ℕ) = (e - 1 - i) + 2 := by omega
      rw [h]; push_cast; ring
    rw [c₁, c₂]; ring
  rw [Finset.sum_sub_distrib, hrefl, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hper,
    Finset.sum_add_distrib, ← Finset.mul_sum, hIco,
    Finset.sum_range_sub (fun k => ((e + 1 - k : ℕ) : K) * Gz w (k : ℤ)) e]
  have hf_e : (e + 1 - e : ℕ) = 1 := by omega
  have hf_0 : (e + 1 - 0 : ℕ) = e + 1 := by omega
  rw [hf_e, hf_0]
  simp only [Nat.cast_one, Nat.cast_zero, Gz_zero, mul_zero, one_mul, sub_zero]
  ring

theorem sum_succ_mul_Gz_sub_eq_Gz_one_mul_tent (w : K) (hw0 : w ≠ 0) (e : ℕ) :
    ∑ i ∈ Finset.range e,
        (((i + 1 : ℕ) : K) * Gz w ((e - i : ℕ) : ℤ) - ((e - 1 - i : ℕ) : K) * Gz w (i : ℤ))
      = Gz w 1 * tent w e :=
  (sum_succ_mul_Gz_sub_eq_sum w e).trans (Gz_one_mul_tent_eq_sum w hw0 e).symm

theorem sum_pred_mul_Gz_sub_eq_Gz_one_mul_tent (w : K) (hw0 : w ≠ 0) (e : ℕ) :
    ∑ i ∈ Finset.range e,
        (((e - i : ℕ) : K) * Gz w ((i + 1 : ℕ) : ℤ) - ((i : ℕ) : K) * Gz w ((e - 1 - i : ℕ) : ℤ))
      = Gz w 1 * tent w e := by
  rw [← sum_succ_mul_Gz_sub_eq_Gz_one_mul_tent w hw0 e,
    ← Finset.sum_range_reflect
      (fun i => ((i + 1 : ℕ) : K) * Gz w ((e - i : ℕ) : ℤ) - ((e - 1 - i : ℕ) : K) * Gz w (i : ℤ))
      e]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hie := Finset.mem_range.mp hi
  have h₁ : e - 1 - i + 1 = e - i := by omega
  have h₂ : e - (e - 1 - i) = i + 1 := by omega
  have h₃ : e - 1 - (e - 1 - i) = i := by omega
  rw [h₁, h₂, h₃]

end Collection
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

section WFamily

private theorem xfun_mul_Gz_split_succ_BDiffWFamily (hu0 : u ≠ 0) (hu1 : u ≠ 1) (i : ℕ) :
    xfun u * Gz u ((i + 1 : ℕ) : ℤ)
      = ((i + 1 : ℕ) : K) * (xfun u * Gz u 1)
        + Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j) := by
  have h := xfun_mul_Gz_split hu0 hu1 (i + 1)
  simpa only [Nat.add_sub_cancel] using h

theorem xfun_sub_mul_xfun_sub_mul_Fz_sub_eq_antidiagonal (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (e : ℕ) :
    (xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (Fz u (e : ℤ) - Fz v (e : ℤ)))
      = ∑ i ∈ Finset.range e,
          ((xfun u * Gz u ((i + 1 : ℕ) : ℤ)) * (xfun v * Gz v ((e - i : ℕ) : ℤ))
            - (xfun u * Gz u ((e - 1 - i : ℕ) : ℤ)) * (xfun v * Gz v (i : ℤ))) := by
  have hxsub := xfun_sub_xfun_eq hu0 hv0 hu1 hv1
  have hexp := xfun_sub_mul_Fz_sub_mul_Fz_sub_expansion hu0 hv0 huvm huvd 1 e
  simp only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_one, zero_add] at hexp

  have hstep : (xfun (u * v) - xfun (u * v⁻¹))
        * ((xfun u - xfun v) * (Fz u (e : ℤ) - Fz v (e : ℤ)))
      = -(xfun u * xfun v)
          * ∑ i ∈ Finset.range e,
              (Gz u ((i : ℤ) + 1) * Gz v ((i : ℤ) + 1 - 1 - (e : ℤ))
                - Gz u ((i : ℤ) + 1 - (e : ℤ)) * Gz v ((i : ℤ) + 1 - 1)) := by
    linear_combination
      ((xfun (u * v) - xfun (u * v⁻¹)) * (Fz u (e : ℤ) - Fz v (e : ℤ))) * hxsub
        + (-(xfun u * xfun v)) * hexp
  rw [hstep, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hie := Finset.mem_range.mp hi

  have g1 : Gz u ((i : ℤ) + 1) = Gz u ((i + 1 : ℕ) : ℤ) := by
    rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 from by push_cast; ring]
  have g2 : Gz v ((i : ℤ) + 1 - 1 - (e : ℤ)) = -Gz v ((e - i : ℕ) : ℤ) := by
    rw [show (i : ℤ) + 1 - 1 - (e : ℤ) = -(((e - i : ℕ) : ℤ)) from by omega, Gz_neg]
  have g3 : Gz u ((i : ℤ) + 1 - (e : ℤ)) = -Gz u ((e - 1 - i : ℕ) : ℤ) := by
    rw [show (i : ℤ) + 1 - (e : ℤ) = -(((e - 1 - i : ℕ) : ℤ)) from by omega, Gz_neg]
  have g4 : Gz v ((i : ℤ) + 1 - 1) = Gz v (i : ℤ) := by
    rw [show (i : ℤ) + 1 - 1 = (i : ℤ) from by ring]
  rw [g1, g2, g3, g4]
  ring

theorem xfun_sub_mul_xfun_sub_mul_Fz_sub_eq_carrier (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (e : ℕ) :
    (xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (Fz u (e : ℤ) - Fz v (e : ℤ)))
      = (xfun u * Gz u 1) * (xfun v * Gz v 1) * (tent u e + tent v e - (e : K) ^ 2)
        + ∑ i ∈ Finset.range e,
            ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j))
                * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j))
              - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2), tent u (e - 1 - i - 1 - 2 * j))
                * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j))) := by
  rw [xfun_sub_mul_xfun_sub_mul_Fz_sub_eq_antidiagonal hu0 hv0 hu1 hv1 huvm huvd e]

  have hterm : ∀ i ∈ Finset.range e,
      (xfun u * Gz u ((i + 1 : ℕ) : ℤ)) * (xfun v * Gz v ((e - i : ℕ) : ℤ))
          - (xfun u * Gz u ((e - 1 - i : ℕ) : ℤ)) * (xfun v * Gz v (i : ℤ))
        = (xfun u * Gz u 1)
              * (((i + 1 : ℕ) : K) * (xfun v * Gz v ((e - i : ℕ) : ℤ))
                - ((e - 1 - i : ℕ) : K) * (xfun v * Gz v (i : ℤ)))
            + ((xfun v * Gz v 1)
                  * (((e - i : ℕ) : K)
                        * (Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j))
                    - ((i : ℕ) : K)
                        * (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2),
                            tent u (e - 1 - i - 1 - 2 * j)))
              + ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j))
                    * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j))
                  - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2),
                        tent u (e - 1 - i - 1 - 2 * j))
                    * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j)))) := by
    intro i hi
    rw [xfun_mul_Gz_split_succ_BDiffWFamily hu0 hu1 i, xfun_mul_Gz_split hu0 hu1 (e - 1 - i),
      xfun_mul_Gz_split hv0 hv1 (e - i), xfun_mul_Gz_split hv0 hv1 i]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]

  have hS1 : ∑ i ∈ Finset.range e,
        (((i + 1 : ℕ) : K) * (xfun v * Gz v ((e - i : ℕ) : ℤ))
          - ((e - 1 - i : ℕ) : K) * (xfun v * Gz v (i : ℤ)))
      = xfun v * (Gz v 1 * tent v e) := by
    have h : ∀ i ∈ Finset.range e,
        ((i + 1 : ℕ) : K) * (xfun v * Gz v ((e - i : ℕ) : ℤ))
            - ((e - 1 - i : ℕ) : K) * (xfun v * Gz v (i : ℤ))
          = xfun v * (((i + 1 : ℕ) : K) * Gz v ((e - i : ℕ) : ℤ)
              - ((e - 1 - i : ℕ) : K) * Gz v (i : ℤ)) := fun i _ => by ring
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum,
      sum_succ_mul_Gz_sub_eq_Gz_one_mul_tent v hv0 e]

  have hS2 : ∑ i ∈ Finset.range e,
        (((e - i : ℕ) : K) * (Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j))
          - ((i : ℕ) : K)
              * (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2), tent u (e - 1 - i - 1 - 2 * j)))
      = xfun u * (Gz u 1 * tent u e) - (e : K) ^ 2 * (xfun u * Gz u 1) := by
    have hper2 : ∀ i ∈ Finset.range e,
        ((e - i : ℕ) : K) * (Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j))
            - ((i : ℕ) : K)
                * (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2),
                    tent u (e - 1 - i - 1 - 2 * j))
          = xfun u * (((e - i : ℕ) : K) * Gz u ((i + 1 : ℕ) : ℤ)
                - ((i : ℕ) : K) * Gz u ((e - 1 - i : ℕ) : ℤ))
            - (((e - i : ℕ) : K) * ((i + 1 : ℕ) : K) - ((i : ℕ) : K) * ((e - 1 - i : ℕ) : K))
                * (xfun u * Gz u 1) := by
      intro i _
      have h1 := xfun_mul_Gz_split_succ_BDiffWFamily hu0 hu1 i
      have h2 := xfun_mul_Gz_split hu0 hu1 (e - 1 - i)
      linear_combination (-((e - i : ℕ) : K)) * h1 + ((i : ℕ) : K) * h2
    have hcoeff : ∑ i ∈ Finset.range e,
          (((e - i : ℕ) : K) * ((i + 1 : ℕ) : K) - ((i : ℕ) : K) * ((e - 1 - i : ℕ) : K))
        = (e : K) ^ 2 := by
      have hper : ∀ i ∈ Finset.range e,
          ((e - i : ℕ) : K) * ((i + 1 : ℕ) : K) - ((i : ℕ) : K) * ((e - 1 - i : ℕ) : K)
            = (e : K) := by
        intro i hi
        have hie := Finset.mem_range.mp hi
        have h1 : ((e - i : ℕ) : K) = (e : K) - (i : K) := by
          have h : (i : K) + ((e - i : ℕ) : K) = (e : K) := by
            rw [← Nat.cast_add]
            congr 1
            omega
          linear_combination h
        have h2 : ((e - 1 - i : ℕ) : K) = (e : K) - 1 - (i : K) := by
          have h : ((i : K) + 1) + ((e - 1 - i : ℕ) : K) = (e : K) := by
            rw [show ((i : K) + 1) = ((i + 1 : ℕ) : K) from by push_cast; ring, ← Nat.cast_add]
            congr 1
            omega
          linear_combination h
        rw [h1, h2]
        push_cast
        ring
      rw [Finset.sum_congr rfl hper, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl hper2, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      sum_pred_mul_Gz_sub_eq_Gz_one_mul_tent u hu0 e, hcoeff]
  rw [hS1, hS2]
  ring

theorem xfun_sub_mul_xfun_sub_mul_Fz_sub_eq_carrier_split [CharZero K] (hu0 : u ≠ 0)
    (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (e : ℕ) :
    (xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (Fz u (e : ℤ) - Fz v (e : ℤ)))
      = (e : K) ^ 2 * ((xfun u * Gz u 1) * (xfun v * Gz v 1))
        + (xfun u * Gz u 1) * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz v 1 * tent v m))
        + (xfun v * Gz v 1) * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz u 1 * tent u m))
        + ∑ i ∈ Finset.range e,
            ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j))
                * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j))
              - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2), tent u (e - 1 - i - 1 - 2 * j))
                * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j))) := by
  rw [xfun_sub_mul_xfun_sub_mul_Fz_sub_eq_carrier hu0 hv0 hu1 hv1 huvm huvd e]
  linear_combination (xfun v * Gz v 1) * xfunG1_mul_tent hu0 hu1 e
    + (xfun u * Gz u 1) * xfunG1_mul_tent hv0 hv1 e

end WFamily
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_B_exports.TateCurve"

theorem solution :

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (w : K) (hw0 : w ≠ 0) (e : ℕ),
      Gz w 1 * tent w e = 2 * ∑ j ∈ Finset.Ico 1 e, Gz w (j : ℤ) + Gz w (e : ℤ)) ∧

    (∀ {β : Type u_1} [AddCommMonoid β] (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → β),
      ∑ x ∈ Sols N, F x = ∑ x ∈ Sols N, F (swap₁ x)) ∧

    (∀ {A : Type u_1} [CommRing A] (f : ℤ → A) (hf0 : f 0 = 0) (hfneg : ∀ a : ℤ, f (-a) = f a) (M : ℕ),
      6 * ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * (f ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + f ((x.1 : ℤ) - (x.2.2.1 : ℤ)) - 2 * f (x.1 : ℤ) - 2 * f (x.2.2.1 : ℤ)) = ∑ δ ∈ M.divisors, ((δ : A) ^ 3 - (δ : A)) * f (δ : ℤ) - 12 * ∑ δ ∈ M.divisors, ∑ k ∈ Finset.Ico 1 δ, (δ : A) * ((δ : A) - (k : A)) * f (k : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) (e : ℕ),
      xfun u * Gz u (e : ℤ) = (e : K) * (xfun u * Gz u 1) + Gz u 1 * ∑ j ∈ Finset.range (e / 2), tent u (e - 1 - 2 * j)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (n : ℕ),
      xCoeff u n - xCoeff v n = ∑ f ∈ n.divisors, (f : K) * (Fz u (f : ℤ) - Fz v (f : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0)
    (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (e : ℕ),
      (xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (Fz u (e : ℤ) - Fz v (e : ℤ))) = (e : K) ^ 2 * ((xfun u * Gz u 1) * (xfun v * Gz v 1)) + (xfun u * Gz u 1) * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz v 1 * tent v m)) + (xfun v * Gz v 1) * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz u 1 * tent u m)) + ∑ i ∈ Finset.range e, ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j)) - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2), tent u (e - 1 - i - 1 - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    {M : ℕ} (hM : 0 < M),
      svComplex u v M = 2 * ((xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M))) - 2 * (xfun u * xfun v) * (∑ d ∈ M.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) + (∑ d ∈ M.divisors, (d : K) * (Gz v (d : ℤ) * ((xfun u * Gz u 1) * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)) + Gz u (d : ℤ) * ((xfun v * Gz v 1) * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)))) + (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (2 * ∑ f ∈ (M - a).divisors, (f : K) * (tent u f + tent v f))) - ∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (2 * (xfun u * xCoeff v (M - a) + xfun v * xCoeff u (M - a)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] {v : K} (a : ℤ),
      Fz v⁻¹ a = Fz v a) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (c d : ℕ → K) (N : ℕ),
      cauchyMul c d N = cauchyMul d c N) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [CharZero K] {v : K} (hv : v ≠ 0) (M : ℕ),
      (∑ e ∈ M.divisors, (e : K) ^ 3 * Fz v (e : ℤ)) + 12 * (sigma 3 M : K) = 6 * cauchyMulInt (xCoeffFull v) (xCoeffFull v) M + xCoeff v M + 12 * ∑ d ∈ M.divisors, (d : K) * tent v d) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (d : ℕ),
      (xfun (u * v) + xfun (u * v⁻¹)) * ((xfun u - xfun v) * (Fz u (d : ℤ) - Fz v (d : ℤ))) = -(((u - v) * (u ^ d - v ^ d) * (∑ i ∈ Finset.range d, (u * v) ^ i) * ((u * v) ^ d)⁻¹ + (u - v⁻¹) * (u ^ d - (v ^ d)⁻¹) * (∑ i ∈ Finset.range d, (u * v⁻¹) ^ i) * ((u * v⁻¹) ^ d)⁻¹) * (xfun u * xfun v))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] (u v : K) (M : ℕ),
      xCoeff u M - xCoeff v M = ∑ d ∈ M.divisors, (d : K) * (Fz u (d : ℤ) - Fz v (d : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (n : ℕ),
      xCoeff (u * v) n + xCoeff (u * v⁻¹) n = ∑ d ∈ n.divisors, (d : K) * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] (v : K) (N : ℕ),
      xCoeff v N = ∑ d ∈ N.divisors, (d : K) * Fz v (d : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (huv1 : u * v ≠ 1)
    (a b : ℕ),
      xfun (u * v) * ((Fz u (a : ℤ) - Fz v (a : ℤ)) * (Fz u (b : ℤ) - Fz v (b : ℤ))) = (u ^ a - v ^ a) * (u ^ b - v ^ b) * (u * v * (∑ i ∈ Finset.range a, (u * v) ^ i) * (∑ i ∈ Finset.range b, (u * v) ^ i) * ((u * v) ^ a)⁻¹ * ((u * v) ^ b)⁻¹)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (huv1 : u * v⁻¹ ≠ 1)
    (a b : ℕ),
      xfun (u * v⁻¹) * ((Fz u (a : ℤ) - Fz v (a : ℤ)) * (Fz u (b : ℤ) - Fz v (b : ℤ))) = (u ^ a - (v ^ a)⁻¹) * (u ^ b - (v ^ b)⁻¹) * (u * v⁻¹ * (∑ i ∈ Finset.range a, (u * v⁻¹) ^ i) * (∑ i ∈ Finset.range b, (u * v⁻¹) ^ i) * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ b)⁻¹)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) {M : ℕ} (hM : 0 < M),
      addDefectSumCoeff u v M = ((xfun (u * v) + xfun (u * v⁻¹)) * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) M + 2 * ((xfun (u * v) + xfun (u * v⁻¹)) * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M))) + (xCoeff (u * v) M + xCoeff (u * v⁻¹) M) * (xfun u - xfun v) ^ 2 + ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a))) + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))) - (2 * (xfun u ^ 2 * xCoeff v M) + 4 * (xfun u * xfun v * xCoeff u M) + 4 * (xfun u * cauchyMulInt (xCoeffFull u) (xCoeffFull v) M) + 2 * (xfun v * cauchyMulInt (xCoeffFull u) (xCoeffFull u) M) + 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M) - (4 * (xfun u * xfun v * xCoeff v M) + 2 * (xfun u * cauchyMulInt (xCoeffFull v) (xCoeffFull v) M) + 2 * (xfun v ^ 2 * xCoeff u M) + 4 * (xfun v * cauchyMulInt (xCoeffFull u) (xCoeffFull v) M) + 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M) - (xfun u * xCoeff v M + xfun v * xCoeff u M + cauchyMulInt (xCoeffFull u) (xCoeffFull v) M) - (2 * (a₄Coeff M * xfun u) + 2 * cauchyMulInt a₄Coeff (xCoeffFull u) M) - (2 * (a₄Coeff M * xfun v) + 2 * cauchyMulInt a₄Coeff (xCoeffFull v) M) - 4 * a₆Coeff M) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ e ∈ (M - i).divisors, (d : K) ^ 2 * (e : K) ^ 2 * (Gz u (d : ℤ) * Gz v (e : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu : u ≠ 0) (a b c : ℤ),
      Fz u a * Fz u b * Gz u c = Gz u (a + b + c) - Gz u (a + b - c) + Gz u (a - b + c) - Gz u (a - b - c) - 2 * Gz u (a + c) + 2 * Gz u (a - c) - 2 * Gz u (b + c) + 2 * Gz u (b - c) + 4 * Gz u c) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0)
    (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M),
      addDefectDiffCoeff u v M = (∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ e ∈ (M - b).divisors, (d : K) * (e : K) * ∑ i ∈ Finset.range d, ∑ i' ∈ Finset.range e, (Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - d - e) - Gz u ((i : ℤ) + i' + 1 - e) * Gz v ((i : ℤ) + i' + 1 - d))) + (∑ b ∈ Finset.Ico 1 M, (∑ d ∈ b.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - b)) + cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M + svComplex u v M) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (M : ℕ),
      ∑ b ∈ Finset.Ico 1 M, (∑ d ∈ b.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - b) = ∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ c ∈ Finset.Ico 1 (M - b), ∑ e ∈ c.divisors, ∑ f ∈ (M - b - c).divisors, (d : K) * (e : K) * (f : K) * ((Gz u ((e : ℤ) + f + d) - Gz u ((e : ℤ) + f - d) + Gz u ((e : ℤ) - f + d) - Gz u ((e : ℤ) - f - d) - 2 * Gz u ((e : ℤ) + d) + 2 * Gz u ((e : ℤ) - d) - 2 * Gz u ((f : ℤ) + d) + 2 * Gz u ((f : ℤ) - d) + 4 * Gz u (d : ℤ)) * Gz v (d : ℤ) - (Gz u ((e : ℤ) + d) - Gz u ((e : ℤ) - d) - 2 * Gz u (d : ℤ)) * (Gz v ((f : ℤ) + d) - Gz v ((f : ℤ) - d) - 2 * Gz v (d : ℤ)) - (Gz u ((f : ℤ) + d) - Gz u ((f : ℤ) - d) - 2 * Gz u (d : ℤ)) * (Gz v ((e : ℤ) + d) - Gz v ((e : ℤ) - d) - 2 * Gz v (d : ℤ)) + Gz u (d : ℤ) * (Gz v ((e : ℤ) + f + d) - Gz v ((e : ℤ) + f - d) + Gz v ((e : ℤ) - f + d) - Gz v ((e : ℤ) - f - d) - 2 * Gz v ((e : ℤ) + d) + 2 * Gz v ((e : ℤ) - d) - 2 * Gz v ((f : ℤ) + d) + 2 * Gz v ((f : ℤ) - d) + 4 * Gz v (d : ℤ)))) :=
  ⟨TateCurve.Gz_one_mul_tent_eq_sum,
   TateCurve.sum_swap₁_total,
   TateCurve.phi_general,
   TateCurve.xfun_mul_Gz_split,
   TateCurve.xCoeff_sub_xCoeff_eq_divisorSum,
   TateCurve.xfun_sub_mul_xfun_sub_mul_Fz_sub_eq_carrier_split,
   TateCurve.svComplex_eq_simplePoleForm,
   TateCurve.Fz_inv,
   TateCurve.cauchyMul_comm,
   TateCurve.phi_identity,
   TateCurve.xfun_add_mul_xfun_sub_mul_Fz_sub,
   TateCurve.xCoeff_sub_xCoeff_divisorSum,
   TateCurve.xCoeff_mul_add_xCoeff_mul_inv,
   TateCurve.xCoeff_eq_sum_mul_Fz,
   TateCurve.xfun_mul_mul_Fz_sub_mul_Fz_sub,
   TateCurve.xfun_mul_inv_mul_Fz_sub_mul_Fz_sub,
   TateCurve.addDefectSumCoeff_eq_boundary_add_int,
   TateCurve.cauchyMulInt_psiCoeffFull_eq_rows,
   TateCurve.Fz_mul_Fz_mul_Gz,
   TateCurve.addDefectDiffCoeff_eq_absorbed,
   TateCurve.crossInterior_block_eq_rows⟩

end S_TateCurve_ks17_B_exports
end P2MW
export P2MW.S_TateCurve_ks17_B_exports (solution)
