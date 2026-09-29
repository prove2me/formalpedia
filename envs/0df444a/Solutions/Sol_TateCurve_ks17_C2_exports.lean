-- Prove2me | solution 1 for TateCurve.ks17_C2_exports
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/52e30254-7efc-59ff-86d1-ce122c5dea60

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_DefectLines
import Definitions.Def_NumberTheory_DivisorConvolution
import Definitions.Def_TateCurve_KeystoneVocab

import Theorems.Thm_TateCurve_ks17_A_exports
import Theorems.Thm_TateCurve_ks17_B_exports
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

namespace P2MW.S_TateCurve_ks17_C2_exports

open scoped NNReal
p2m_open "TateCurve P2MW.S_TateCurve_ks17_C2_exports.TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset"

universe u_1 u_2

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz Fz_natCast Fz_mul_Fz xDivTerm_eq_mul_Fz a₆Coeff_of_pos tent xfun_mul_Fz_eq_tent cauchyMulInt_a4x_eq_neg_sum_Sols tent_eq_sq_add_sum_Ico add_le_of_mem_Sols cauchyMul xCoeffFull xCoeffFull_succ a₄Coeff a₄Coeff_succ a₆Coeff xfun yfun xfun_inv pointX pointY term b b_mul_twelve a₄ a₆ curve xDivTerm xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports"
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

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz Fz_natCast Fz_mul_Fz xDivTerm_eq_mul_Fz a₆Coeff_of_pos tent xfun_mul_Fz_eq_tent cauchyMulInt_a4x_eq_neg_sum_Sols tent_eq_sq_add_sum_Ico add_le_of_mem_Sols cauchyMul xCoeffFull xCoeffFull_succ a₄Coeff a₄Coeff_succ a₆Coeff xfun yfun xfun_inv pointX pointY term b b_mul_twelve a₄ a₆ curve xDivTerm xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

theorem Gz_one_mul_tent_eq_sum : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (w : K) (hw0 : w ≠ 0) (e : ℕ),
      Gz w 1 * tent w e = 2 * ∑ j ∈ Finset.Ico 1 e, Gz w (j : ℤ) + Gz w (e : ℤ) :=
  TateCurve.ks17_B_exports.{u_1}.1

theorem sum_swap₁_total : ∀ {β : Type u_1} [AddCommMonoid β] (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → β),
      ∑ x ∈ Sols N, F x = ∑ x ∈ Sols N, F (swap₁ x) :=
  TateCurve.ks17_B_exports.{u_1}.2.1

theorem phi_general : ∀ {A : Type u_1} [CommRing A] (f : ℤ → A) (hf0 : f 0 = 0) (hfneg : ∀ a : ℤ, f (-a) = f a) (M : ℕ),
      6 * ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * (f ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + f ((x.1 : ℤ) - (x.2.2.1 : ℤ)) - 2 * f (x.1 : ℤ) - 2 * f (x.2.2.1 : ℤ)) = ∑ δ ∈ M.divisors, ((δ : A) ^ 3 - (δ : A)) * f (δ : ℤ) - 12 * ∑ δ ∈ M.divisors, ∑ k ∈ Finset.Ico 1 δ, (δ : A) * ((δ : A) - (k : A)) * f (k : ℤ) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.1

theorem xfun_mul_Gz_split : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) (e : ℕ),
      xfun u * Gz u (e : ℤ) = (e : K) * (xfun u * Gz u 1) + Gz u 1 * ∑ j ∈ Finset.range (e / 2), tent u (e - 1 - 2 * j) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.1

theorem xCoeff_sub_xCoeff_eq_divisorSum : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (n : ℕ),
      xCoeff u n - xCoeff v n = ∑ f ∈ n.divisors, (f : K) * (Fz u (f : ℤ) - Fz v (f : ℤ)) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.1

theorem xfun_sub_mul_xfun_sub_mul_Fz_sub_eq_carrier_split : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0)
    (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (e : ℕ),
      (xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (Fz u (e : ℤ) - Fz v (e : ℤ))) = (e : K) ^ 2 * ((xfun u * Gz u 1) * (xfun v * Gz v 1)) + (xfun u * Gz u 1) * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz v 1 * tent v m)) + (xfun v * Gz v 1) * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz u 1 * tent u m)) + ∑ i ∈ Finset.range e, ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j)) - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2), tent u (e - 1 - i - 1 - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j))) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.1

theorem svComplex_eq_simplePoleForm : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    {M : ℕ} (hM : 0 < M),
      svComplex u v M = 2 * ((xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M))) - 2 * (xfun u * xfun v) * (∑ d ∈ M.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) + (∑ d ∈ M.divisors, (d : K) * (Gz v (d : ℤ) * ((xfun u * Gz u 1) * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)) + Gz u (d : ℤ) * ((xfun v * Gz v 1) * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)))) + (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (2 * ∑ f ∈ (M - a).divisors, (f : K) * (tent u f + tent v f))) - ∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (2 * (xfun u * xCoeff v (M - a) + xfun v * xCoeff u (M - a))) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.1

theorem Fz_inv : ∀ {K : Type u_1} [NontriviallyNormedField K] {v : K} (a : ℤ),
      Fz v⁻¹ a = Fz v a :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.1

theorem cauchyMul_comm : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (c d : ℕ → K) (N : ℕ),
      cauchyMul c d N = cauchyMul d c N :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.1

theorem phi_identity : ∀ {K : Type u_1} [NontriviallyNormedField K] [CharZero K] {v : K} (hv : v ≠ 0) (M : ℕ),
      (∑ e ∈ M.divisors, (e : K) ^ 3 * Fz v (e : ℤ)) + 12 * (sigma 3 M : K) = 6 * cauchyMulInt (xCoeffFull v) (xCoeffFull v) M + xCoeff v M + 12 * ∑ d ∈ M.divisors, (d : K) * tent v d :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.2.1

theorem xfun_add_mul_xfun_sub_mul_Fz_sub : ∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (d : ℕ),
      (xfun (u * v) + xfun (u * v⁻¹)) * ((xfun u - xfun v) * (Fz u (d : ℤ) - Fz v (d : ℤ))) = -(((u - v) * (u ^ d - v ^ d) * (∑ i ∈ Finset.range d, (u * v) ^ i) * ((u * v) ^ d)⁻¹ + (u - v⁻¹) * (u ^ d - (v ^ d)⁻¹) * (∑ i ∈ Finset.range d, (u * v⁻¹) ^ i) * ((u * v⁻¹) ^ d)⁻¹) * (xfun u * xfun v)) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.1

theorem xCoeff_sub_xCoeff_divisorSum : ∀ {K : Type u_1} [NontriviallyNormedField K] (u v : K) (M : ℕ),
      xCoeff u M - xCoeff v M = ∑ d ∈ M.divisors, (d : K) * (Fz u (d : ℤ) - Fz v (d : ℤ)) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.1

theorem xCoeff_mul_add_xCoeff_mul_inv : ∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (n : ℕ),
      xCoeff (u * v) n + xCoeff (u * v⁻¹) n = ∑ d ∈ n.divisors, (d : K) * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ)) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem xCoeff_eq_sum_mul_Fz : ∀ {K : Type u_1} [NontriviallyNormedField K] (v : K) (N : ℕ),
      xCoeff v N = ∑ d ∈ N.divisors, (d : K) * Fz v (d : ℤ) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem xfun_mul_mul_Fz_sub_mul_Fz_sub : ∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (huv1 : u * v ≠ 1)
    (a b : ℕ),
      xfun (u * v) * ((Fz u (a : ℤ) - Fz v (a : ℤ)) * (Fz u (b : ℤ) - Fz v (b : ℤ))) = (u ^ a - v ^ a) * (u ^ b - v ^ b) * (u * v * (∑ i ∈ Finset.range a, (u * v) ^ i) * (∑ i ∈ Finset.range b, (u * v) ^ i) * ((u * v) ^ a)⁻¹ * ((u * v) ^ b)⁻¹) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem xfun_mul_inv_mul_Fz_sub_mul_Fz_sub : ∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (huv1 : u * v⁻¹ ≠ 1)
    (a b : ℕ),
      xfun (u * v⁻¹) * ((Fz u (a : ℤ) - Fz v (a : ℤ)) * (Fz u (b : ℤ) - Fz v (b : ℤ))) = (u ^ a - (v ^ a)⁻¹) * (u ^ b - (v ^ b)⁻¹) * (u * v⁻¹ * (∑ i ∈ Finset.range a, (u * v⁻¹) ^ i) * (∑ i ∈ Finset.range b, (u * v⁻¹) ^ i) * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ b)⁻¹) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem addDefectSumCoeff_eq_boundary_add_int : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) {M : ℕ} (hM : 0 < M),
      addDefectSumCoeff u v M = ((xfun (u * v) + xfun (u * v⁻¹)) * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) M + 2 * ((xfun (u * v) + xfun (u * v⁻¹)) * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M))) + (xCoeff (u * v) M + xCoeff (u * v⁻¹) M) * (xfun u - xfun v) ^ 2 + ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a))) + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))) - (2 * (xfun u ^ 2 * xCoeff v M) + 4 * (xfun u * xfun v * xCoeff u M) + 4 * (xfun u * cauchyMulInt (xCoeffFull u) (xCoeffFull v) M) + 2 * (xfun v * cauchyMulInt (xCoeffFull u) (xCoeffFull u) M) + 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M) - (4 * (xfun u * xfun v * xCoeff v M) + 2 * (xfun u * cauchyMulInt (xCoeffFull v) (xCoeffFull v) M) + 2 * (xfun v ^ 2 * xCoeff u M) + 4 * (xfun v * cauchyMulInt (xCoeffFull u) (xCoeffFull v) M) + 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M) - (xfun u * xCoeff v M + xfun v * xCoeff u M + cauchyMulInt (xCoeffFull u) (xCoeffFull v) M) - (2 * (a₄Coeff M * xfun u) + 2 * cauchyMulInt a₄Coeff (xCoeffFull u) M) - (2 * (a₄Coeff M * xfun v) + 2 * cauchyMulInt a₄Coeff (xCoeffFull v) M) - 4 * a₆Coeff M :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cauchyMulInt_psiCoeffFull_eq_rows : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ e ∈ (M - i).divisors, (d : K) ^ 2 * (e : K) ^ 2 * (Gz u (d : ℤ) * Gz v (e : ℤ)) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Fz_mul_Fz_mul_Gz : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu : u ≠ 0) (a b c : ℤ),
      Fz u a * Fz u b * Gz u c = Gz u (a + b + c) - Gz u (a + b - c) + Gz u (a - b + c) - Gz u (a - b - c) - 2 * Gz u (a + c) + 2 * Gz u (a - c) - 2 * Gz u (b + c) + 2 * Gz u (b - c) + 4 * Gz u c :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem addDefectDiffCoeff_eq_absorbed : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0)
    (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M),
      addDefectDiffCoeff u v M = (∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ e ∈ (M - b).divisors, (d : K) * (e : K) * ∑ i ∈ Finset.range d, ∑ i' ∈ Finset.range e, (Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - d - e) - Gz u ((i : ℤ) + i' + 1 - e) * Gz v ((i : ℤ) + i' + 1 - d))) + (∑ b ∈ Finset.Ico 1 M, (∑ d ∈ b.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - b)) + cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M + svComplex u v M :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem crossInterior_block_eq_rows : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (M : ℕ),
      ∑ b ∈ Finset.Ico 1 M, (∑ d ∈ b.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - b) = ∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ c ∈ Finset.Ico 1 (M - b), ∑ e ∈ c.divisors, ∑ f ∈ (M - b - c).divisors, (d : K) * (e : K) * (f : K) * ((Gz u ((e : ℤ) + f + d) - Gz u ((e : ℤ) + f - d) + Gz u ((e : ℤ) - f + d) - Gz u ((e : ℤ) - f - d) - 2 * Gz u ((e : ℤ) + d) + 2 * Gz u ((e : ℤ) - d) - 2 * Gz u ((f : ℤ) + d) + 2 * Gz u ((f : ℤ) - d) + 4 * Gz u (d : ℤ)) * Gz v (d : ℤ) - (Gz u ((e : ℤ) + d) - Gz u ((e : ℤ) - d) - 2 * Gz u (d : ℤ)) * (Gz v ((f : ℤ) + d) - Gz v ((f : ℤ) - d) - 2 * Gz v (d : ℤ)) - (Gz u ((f : ℤ) + d) - Gz u ((f : ℤ) - d) - 2 * Gz u (d : ℤ)) * (Gz v ((e : ℤ) + d) - Gz v ((e : ℤ) - d) - 2 * Gz v (d : ℤ)) + Gz u (d : ℤ) * (Gz v ((e : ℤ) + f + d) - Gz v ((e : ℤ) + f - d) + Gz v ((e : ℤ) - f + d) - Gz v ((e : ℤ) - f - d) - 2 * Gz v ((e : ℤ) + d) + 2 * Gz v ((e : ℤ) - d) - 2 * Gz v ((f : ℤ) + d) + 2 * Gz v ((f : ℤ) - d) + 4 * Gz v (d : ℤ))) :=
  TateCurve.ks17_B_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz Fz_natCast Fz_mul_Fz xDivTerm_eq_mul_Fz a₆Coeff_of_pos tent xfun_mul_Fz_eq_tent cauchyMulInt_a4x_eq_neg_sum_Sols tent_eq_sq_add_sum_Ico add_le_of_mem_Sols cauchyMul xCoeffFull xCoeffFull_succ a₄Coeff a₄Coeff_succ a₆Coeff xfun yfun xfun_inv pointX pointY term b b_mul_twelve a₄ a₆ curve xDivTerm xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] {u v w : K}

section SmallHelpers

theorem xCoeff_inv (w : K) (N : ℕ) : xCoeff w⁻¹ N = xCoeff w N := by
  rw [xCoeff, xCoeff]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz, Fz_inv]

theorem xfun_mul_xCoeff_eq_sum_tent (hw0 : w ≠ 0) (hw1 : w ≠ 1) (N : ℕ) :
    xfun w * xCoeff w N = ∑ d ∈ N.divisors, (d : K) * tent w d := by
  rw [xCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [xDivTerm_eq_mul_Fz, ← xfun_mul_Fz_eq_tent hw0 hw1 d]
  ring

theorem xfun_sq_mul_Fz [CharZero K] (hw0 : w ≠ 0) (hw1 : w ≠ 1) (d : ℕ) :
    xfun w ^ 2 * Fz w (d : ℤ)
      = (d : K) ^ 2 * xfun w + ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent w k := by
  have h1 : xfun w ^ 2 * Fz w (d : ℤ) = xfun w * tent w d := by
    rw [← xfun_mul_Fz_eq_tent hw0 hw1 d]
    ring
  rw [h1, tent_eq_sq_add_sum_Ico hw0 hw1 d, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [← xfun_mul_Fz_eq_tent hw0 hw1 k]
    ring

theorem cauchyMul_left_comm (a b c : ℕ → K) (N : ℕ) :
    cauchyMul a (cauchyMul b c) N = cauchyMul b (cauchyMul a c) N := by
  have key : ∀ x y : ℕ → K, cauchyMul x (cauchyMul y c) N
      = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1 - i), x i * (y j * c (N - i - j)) := by
    intro x y
    rw [cauchyMul_eq_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [cauchyMul_eq_sum_range, Finset.mul_sum]
    rw [show N - i + 1 = N + 1 - i by omega]
  have hswap := Finset.sum_comm' (s := Finset.range (N + 1))
    (t := fun i => Finset.range (N + 1 - i))
    (t' := Finset.range (N + 1)) (s' := fun j => Finset.range (N + 1 - j))
    (f := fun i j => a i * (b j * c (N - i - j)))
    (fun i j => by simp only [Finset.mem_range]; omega)
  rw [key a b, key b a, hswap]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i hi => ?_
  rw [show N - i - j = N - j - i by omega]
  ring

end SmallHelpers

section Swap

variable [IsUltrametricDist K] [CompleteSpace K]

theorem addDefectSumCoeff_swap (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huvd : u * v⁻¹ ≠ 1) (M : ℕ) :
    addDefectSumCoeff v u M = addDefectSumCoeff u v M := by
  have hd0 : u * v⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hv0)

  have hinv : v * u⁻¹ = (u * v⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
  have hXd : xCoeffFull ((u * v⁻¹)⁻¹) = xCoeffFull (u * v⁻¹) := by
    funext N
    cases N with
    | zero => simpa using xfun_inv hd0 huvd
    | succ n => simp only [xCoeffFull_succ]; exact xCoeff_inv _ _
  have hQP : cauchyMul (xCoeffFull v) (xCoeffFull u) = cauchyMul (xCoeffFull u) (xCoeffFull v) := by
    funext N
    exact cauchyMul_comm _ _ N

  have h7 : cauchyMul (xCoeffFull v) (cauchyMul (xCoeffFull u) (xCoeffFull v)) M
      = cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull v) (xCoeffFull v)) M :=
    cauchyMul_left_comm _ _ _ M
  have h8 : cauchyMul (xCoeffFull v) (cauchyMul (xCoeffFull u) (xCoeffFull u)) M
      = cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull u) (xCoeffFull v)) M := by
    rw [cauchyMul_left_comm, hQP]
  simp only [addDefectSumCoeff]
  rw [mul_comm v u, hinv, hXd, hQP]
  linear_combination (-2 : K) * h7 - 2 * h8

end Swap

section PoleDischarge

variable [IsUltrametricDist K]

theorem sameVarPole_discharge [CharZero K] (hv0 : v ≠ 0) (M : ℕ) :
    (∑ d ∈ M.divisors, (d : K) ^ 3 * (Fz v (d : ℤ) + 2))
      - 6 * cauchyMulInt (xCoeffFull v) (xCoeffFull v) M
      - xCoeff v M - 2 * a₄Coeff M
      - 12 * ∑ d ∈ M.divisors, (d : K) * tent v d = 0 := by
  have hphi := phi_identity (K := K) hv0 M
  have hsigma : ((sigma 3 M : ℕ) : K) = ∑ d ∈ M.divisors, (d : K) ^ 3 := by
    simp only [sigma]
    push_cast
    rfl
  have ha4 : a₄Coeff (K := K) M = -(5 * ∑ d ∈ M.divisors, (d : K) ^ 3) := by
    have h : a₄Coeff (K := K) M = -(∑ d ∈ M.divisors, ((5 * d ^ 3 : ℕ) : K)) := by
      cases M with
      | zero => simp
      | succ n => exact a₄Coeff_succ n
    rw [h, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun d _ => by push_cast; ring
  have hsplit : (∑ d ∈ M.divisors, (d : K) ^ 3 * (Fz v (d : ℤ) + 2))
      = (∑ d ∈ M.divisors, (d : K) ^ 3 * Fz v (d : ℤ)) + 2 * ∑ d ∈ M.divisors, (d : K) ^ 3 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hsplit, ha4]
  linear_combination hphi - 12 * hsigma

end PoleDischarge

section LambdaExpansion

private theorem geom_mul_pow_inv_C2RowForm (hw0 : w ≠ 0) (d : ℕ) :
    (∑ i ∈ Finset.range d, w ^ i) * (w ^ d)⁻¹ = ∑ j ∈ Finset.Icc 1 d, (w ^ j)⁻¹ := by
  rw [Finset.sum_mul]
  refine Finset.sum_nbij' (i := fun i => d - i) (j := fun j => d - j) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Icc]
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_range]
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    try dsimp only
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    try dsimp only
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    try dsimp only
    have h : w ^ d = w ^ a * w ^ (d - a) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero a hw0), one_mul]

private theorem mul_mul_geom_mul_pow_inv_C2RowForm (hw0 : w ≠ 0) (A B : K) (d : ℕ) :
    A * B * (∑ i ∈ Finset.range d, w ^ i) * (w ^ d)⁻¹
      = ∑ j ∈ Finset.Icc 1 d, A * B * (w ^ j)⁻¹ := by
  rw [mul_assoc (A * B), geom_mul_pow_inv_C2RowForm hw0 d, Finset.mul_sum]

private theorem lambda_summand_C2RowForm (hu0 : u ≠ 0) (hv0 : v ≠ 0) {d j : ℕ} (hj1 : 1 ≤ j)
    (hjd : j ≤ d) :
    (u - v) * (u ^ d - v ^ d) * ((u * v) ^ j)⁻¹
      + (u - v⁻¹) * (u ^ d - (v ^ d)⁻¹) * ((u * v⁻¹) ^ j)⁻¹
    = u ^ (d + 1 - j) * (v ^ j + (v ^ j)⁻¹)
      + (u ^ j)⁻¹ * (v ^ (d + 1 - j) + (v ^ (d + 1 - j))⁻¹)
      - (u ^ (j - 1))⁻¹ * (v ^ (d - j) + (v ^ (d - j))⁻¹)
      - u ^ (d - j) * (v ^ (j - 1) + (v ^ (j - 1))⁻¹) := by
  have hu' : u ^ (j - 1) ≠ 0 := pow_ne_zero _ hu0
  have hu'' : u ^ (d - j) ≠ 0 := pow_ne_zero _ hu0
  have hv' : v ^ (j - 1) ≠ 0 := pow_ne_zero _ hv0
  have hv'' : v ^ (d - j) ≠ 0 := pow_ne_zero _ hv0
  have hud : u ^ d = u ^ (j - 1) * u ^ (d - j) * u := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have huj : u ^ j = u ^ (j - 1) * u := by
    rw [← pow_succ]
    congr 1
    omega
  have hudj : u ^ (d + 1 - j) = u ^ (d - j) * u := by
    rw [← pow_succ]
    congr 1
    omega
  have hvd : v ^ d = v ^ (j - 1) * v ^ (d - j) * v := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hvj : v ^ j = v ^ (j - 1) * v := by
    rw [← pow_succ]
    congr 1
    omega
  have hvdj : v ^ (d + 1 - j) = v ^ (d - j) * v := by
    rw [← pow_succ]
    congr 1
    omega
  rw [mul_pow, mul_pow, inv_pow, hud, huj, hudj, hvd, hvj, hvdj]
  field_simp
  ring

private theorem sum_Icc_reflect_C2RowForm (f : ℕ → K) (d : ℕ) :
    ∑ j ∈ Finset.Icc 1 d, f j = ∑ j ∈ Finset.Icc 1 d, f (d + 1 - j) := by
  refine Finset.sum_nbij' (i := fun j => d + 1 - j) (j := fun j => d + 1 - j) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    try dsimp only
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    try dsimp only
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    try dsimp only
    congr 1
    omega

private theorem sum_Icc_to_range_pred_C2RowForm (f : ℕ → K) (d : ℕ) :
    ∑ j ∈ Finset.Icc 1 d, f (j - 1) = ∑ j ∈ Finset.range d, f j := by
  refine Finset.sum_nbij' (i := fun j => j - 1) (j := fun j => j + 1) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_range]
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Icc]
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    try dsimp only
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    try dsimp only
    omega
  · intro a _
    rfl

private theorem sum_Icc_to_range_sub_C2RowForm (f : ℕ → K) (d : ℕ) :
    ∑ j ∈ Finset.Icc 1 d, f (d - j) = ∑ j ∈ Finset.range d, f j := by
  refine Finset.sum_nbij' (i := fun j => d - j) (j := fun j => d - j) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_range]
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Icc]
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    try dsimp only
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    try dsimp only
    omega
  · intro a _
    rfl

private theorem sum_Icc_eq_sum_range_add_C2RowForm (f : ℕ → K) (hf0 : f 0 = 0) (d : ℕ) :
    ∑ j ∈ Finset.Icc 1 d, f j = (∑ j ∈ Finset.range d, f j) + f d := by
  induction d with
  | zero => simpa using hf0.symm
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ]

theorem lambda_expansion (hu0 : u ≠ 0) (hv0 : v ≠ 0) (d : ℕ) :
    (u - v) * (u ^ d - v ^ d) * (∑ i ∈ Finset.range d, (u * v) ^ i) * ((u * v) ^ d)⁻¹
      + (u - v⁻¹) * (u ^ d - (v ^ d)⁻¹) * (∑ i ∈ Finset.range d, (u * v⁻¹) ^ i)
          * ((u * v⁻¹) ^ d)⁻¹
    = ((∑ j ∈ Finset.Icc 1 d, Fz v (j : ℤ) * Fz u ((d + 1 - j : ℕ) : ℤ))
        - ∑ j ∈ Finset.range d, Fz v (j : ℤ) * Fz u ((d - 1 - j : ℕ) : ℤ))
      + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ) := by
  have hm0 : u * v ≠ 0 := mul_ne_zero hu0 hv0
  have ht0 : u * v⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hv0)

  rw [mul_mul_geom_mul_pow_inv_C2RowForm hm0 (u - v) (u ^ d - v ^ d) d,
    mul_mul_geom_mul_pow_inv_C2RowForm ht0 (u - v⁻¹) (u ^ d - (v ^ d)⁻¹) d, ← Finset.sum_add_distrib]

  rw [Finset.sum_congr rfl fun j hj => lambda_summand_C2RowForm hu0 hv0 (Finset.mem_Icc.mp hj).1
    (Finset.mem_Icc.mp hj).2]

  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]

  have hf2 : (∑ j ∈ Finset.Icc 1 d, (u ^ j)⁻¹ * (v ^ (d + 1 - j) + (v ^ (d + 1 - j))⁻¹))
      = ∑ j ∈ Finset.Icc 1 d, (u ^ (d + 1 - j))⁻¹ * (v ^ j + (v ^ j)⁻¹) := by
    rw [sum_Icc_reflect_C2RowForm (fun j => (u ^ j)⁻¹ * (v ^ (d + 1 - j) + (v ^ (d + 1 - j))⁻¹)) d]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_Icc.mp hj
    rw [show d + 1 - (d + 1 - j) = j by omega]
  have hf3 : (∑ j ∈ Finset.Icc 1 d, (u ^ (j - 1))⁻¹ * (v ^ (d - j) + (v ^ (d - j))⁻¹))
      = ∑ j ∈ Finset.range d, (u ^ (d - 1 - j))⁻¹ * (v ^ j + (v ^ j)⁻¹) := by
    rw [← sum_Icc_to_range_sub_C2RowForm (fun k => (u ^ (d - 1 - k))⁻¹ * (v ^ k + (v ^ k)⁻¹)) d]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_Icc.mp hj
    rw [show d - 1 - (d - j) = j - 1 by omega]
  have hf4 : (∑ j ∈ Finset.Icc 1 d, u ^ (d - j) * (v ^ (j - 1) + (v ^ (j - 1))⁻¹))
      = ∑ j ∈ Finset.range d, u ^ (d - 1 - j) * (v ^ j + (v ^ j)⁻¹) := by
    rw [← sum_Icc_to_range_pred_C2RowForm (fun k => u ^ (d - 1 - k) * (v ^ k + (v ^ k)⁻¹)) d]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_Icc.mp hj
    rw [show d - 1 - (j - 1) = d - j by omega]
  rw [hf2, hf3, hf4]

  have hexp1 : (∑ j ∈ Finset.Icc 1 d, Fz v (j : ℤ) * Fz u ((d + 1 - j : ℕ) : ℤ))
      = (∑ j ∈ Finset.Icc 1 d, u ^ (d + 1 - j) * (v ^ j + (v ^ j)⁻¹))
        + (∑ j ∈ Finset.Icc 1 d, (u ^ (d + 1 - j))⁻¹ * (v ^ j + (v ^ j)⁻¹))
        - 2 * (∑ j ∈ Finset.Icc 1 d, Fz v (j : ℤ))
        - 2 * (∑ j ∈ Finset.Icc 1 d, Fz u ((d + 1 - j : ℕ) : ℤ))
        - 4 * d := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    rw [show (4 : K) * d = ∑ _j ∈ Finset.Icc 1 d, (4 : K) by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      push_cast
      ring]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Fz_natCast, Fz_natCast]
    simp only [inv_pow]
    ring
  have hexp2 : (∑ j ∈ Finset.range d, Fz v (j : ℤ) * Fz u ((d - 1 - j : ℕ) : ℤ))
      = (∑ j ∈ Finset.range d, u ^ (d - 1 - j) * (v ^ j + (v ^ j)⁻¹))
        + (∑ j ∈ Finset.range d, (u ^ (d - 1 - j))⁻¹ * (v ^ j + (v ^ j)⁻¹))
        - 2 * (∑ j ∈ Finset.range d, Fz v (j : ℤ))
        - 2 * (∑ j ∈ Finset.range d, Fz u ((d - 1 - j : ℕ) : ℤ))
        - 4 * d := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    rw [show (4 : K) * d = ∑ _j ∈ Finset.range d, (4 : K) by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Fz_natCast, Fz_natCast]
    simp only [inv_pow]
    ring

  have htelv : (∑ j ∈ Finset.Icc 1 d, Fz v (j : ℤ))
      = (∑ j ∈ Finset.range d, Fz v (j : ℤ)) + Fz v (d : ℤ) :=
    sum_Icc_eq_sum_range_add_C2RowForm (fun j => Fz v (j : ℤ)) (by simp) d
  have hteluIcc : (∑ j ∈ Finset.Icc 1 d, Fz u ((d + 1 - j : ℕ) : ℤ))
      = (∑ j ∈ Finset.range d, Fz u (j : ℤ)) + Fz u (d : ℤ) := by
    rw [sum_Icc_reflect_C2RowForm (fun j => Fz u ((d + 1 - j : ℕ) : ℤ)) d]
    rw [Finset.sum_congr rfl fun j hj => by
      have hj' := Finset.mem_Icc.mp hj
      rw [show d + 1 - (d + 1 - j) = j by omega]]
    exact sum_Icc_eq_sum_range_add_C2RowForm (fun j => Fz u (j : ℤ)) (by simp) d
  have hrangeu : (∑ j ∈ Finset.range d, Fz u ((d - 1 - j : ℕ) : ℤ))
      = ∑ j ∈ Finset.range d, Fz u (j : ℤ) := by
    exact Finset.sum_range_reflect (fun j => Fz u (j : ℤ)) d
  rw [hexp1, hexp2, htelv, hteluIcc, hrangeu]
  ring

end LambdaExpansion

section MixedCrossTentForm

theorem xfun_add_mul_xfun_sub_mul_Fz_sub_tentForm (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (d : ℕ) :
    (xfun (u * v) + xfun (u * v⁻¹)) * ((xfun u - xfun v) * (Fz u (d : ℤ) - Fz v (d : ℤ)))
      = -(2 * (xfun u * tent v d) + 2 * (xfun v * tent u d)
          + ((∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j))
              - ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j))) := by
  have hbase := xfun_add_mul_xfun_sub_mul_Fz_sub hu0 hv0 hu1 hv1 huvm huvd d
  have hlam := lambda_expansion hu0 hv0 d
  have hsum1 : (∑ j ∈ Finset.Icc 1 d, Fz v (j : ℤ) * Fz u ((d + 1 - j : ℕ) : ℤ))
        * (xfun u * xfun v)
      = ∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← xfun_mul_Fz_eq_tent hv0 hv1 j, ← xfun_mul_Fz_eq_tent hu0 hu1 (d + 1 - j)]
    ring
  have hsum2 : (∑ j ∈ Finset.range d, Fz v (j : ℤ) * Fz u ((d - 1 - j : ℕ) : ℤ))
        * (xfun u * xfun v)
      = ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← xfun_mul_Fz_eq_tent hv0 hv1 j, ← xfun_mul_Fz_eq_tent hu0 hu1 (d - 1 - j)]
    ring
  have htu : Fz u (d : ℤ) * (xfun u * xfun v) = tent u d * xfun v := by
    rw [← xfun_mul_Fz_eq_tent hu0 hu1 d]
    ring
  have htv : Fz v (d : ℤ) * (xfun u * xfun v) = tent v d * xfun u := by
    rw [← xfun_mul_Fz_eq_tent hv0 hv1 d]
    ring
  linear_combination hbase - (xfun u * xfun v) * hlam - hsum1 + hsum2 - 2 * htu - 2 * htv

theorem xfun_add_mul_xfun_sub_mul_xCoeff_sub_tentForm (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (M : ℕ) :
    (xfun (u * v) + xfun (u * v⁻¹)) * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M))
      = -(2 * (xfun u * ∑ d ∈ M.divisors, (d : K) * tent v d)
          + 2 * (xfun v * ∑ d ∈ M.divisors, (d : K) * tent u d)
          + ∑ d ∈ M.divisors, (d : K) *
              ((∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j))
                - ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j))) := by
  have hper : ∀ d ∈ M.divisors,
      (xfun (u * v) + xfun (u * v⁻¹))
          * ((xfun u - xfun v) * ((d : K) * (Fz u (d : ℤ) - Fz v (d : ℤ))))
        = (d : K) * (-(2 * (xfun u * tent v d) + 2 * (xfun v * tent u d)
            + ((∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j))
                - ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j)))) := by
    intro d _
    linear_combination (d : K)
      * xfun_add_mul_xfun_sub_mul_Fz_sub_tentForm hu0 hv0 hu1 hv1 huvm huvd d
  have hexpand : (xfun (u * v) + xfun (u * v⁻¹))
        * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M))
      = ∑ d ∈ M.divisors, (d : K) * (-(2 * (xfun u * tent v d) + 2 * (xfun v * tent u d)
          + ((∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j))
              - ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j)))) := by
    rw [xCoeff_sub_xCoeff_divisorSum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hper
  rw [hexpand, eq_neg_iff_add_eq_zero]
  have hA : (2 : K) * (xfun u * ∑ d ∈ M.divisors, (d : K) * tent v d)
      = ∑ d ∈ M.divisors, 2 * (xfun u * ((d : K) * tent v d)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
  have hB : (2 : K) * (xfun v * ∑ d ∈ M.divisors, (d : K) * tent u d)
      = ∑ d ∈ M.divisors, 2 * (xfun v * ((d : K) * tent u d)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hA, hB, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun d _ => ?_
  ring

end MixedCrossTentForm

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz Fz_natCast Fz_mul_Fz xDivTerm_eq_mul_Fz a₆Coeff_of_pos tent xfun_mul_Fz_eq_tent cauchyMulInt_a4x_eq_neg_sum_Sols tent_eq_sq_add_sum_Ico add_le_of_mem_Sols cauchyMul xCoeffFull xCoeffFull_succ a₄Coeff a₄Coeff_succ a₆Coeff xfun yfun xfun_inv pointX pointY term b b_mul_twelve a₄ a₆ curve xDivTerm xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section Helpers

theorem xfun_mul_crossSum_left (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (a : ℕ) :
    xfun u * (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
      = (∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d)
        + 2 * (xfun u * xCoeff v a) := by
  rw [xCoeff_mul_add_xCoeff_mul_inv hu0 hv0 a, xCoeff_eq_sum_mul_Fz v a, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  have ht := xfun_mul_Fz_eq_tent hu0 hu1 d
  linear_combination ((d : K) * Fz v (d : ℤ) + 2 * (d : K)) * ht

theorem xfun_mul_crossSum_right (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hv1 : v ≠ 1) (a : ℕ) :
    xfun v * (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
      = (∑ d ∈ a.divisors, (d : K) * (Fz u (d : ℤ) + 2) * tent v d)
        + 2 * (xfun v * xCoeff u a) := by
  rw [xCoeff_mul_add_xCoeff_mul_inv hu0 hv0 a, xCoeff_eq_sum_mul_Fz u a, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  have ht := xfun_mul_Fz_eq_tent hv0 hv1 d
  linear_combination ((d : K) * Fz u (d : ℤ) + 2 * (d : K)) * ht

end Helpers

section SquareComplex

private theorem crossSquare_per_divisor_C2AssemblyS1 [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (d : ℕ) :
    (d : K) * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ))
        * (xfun u - xfun v) ^ 2
      - 2 * (xfun u ^ 2 * ((d : K) * Fz v (d : ℤ)))
      - 2 * (xfun v ^ 2 * ((d : K) * Fz u (d : ℤ)))
      - 4 * (xfun u * xfun v * ((d : K) * Fz u (d : ℤ)))
      - 4 * (xfun u * xfun v * ((d : K) * Fz v (d : ℤ)))
    = (d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k)
          + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k)
          - 2 * (tent u d * tent v d))
      + xfun u * ((d : K) ^ 3 * (Fz v (d : ℤ) + 2))
      + xfun v * ((d : K) ^ 3 * (Fz u (d : ℤ) + 2))
      - 8 * (xfun u * ((d : K) * tent v d))
      - 8 * (xfun v * ((d : K) * tent u d)) := by
  have hsqu := xfun_sq_mul_Fz hu0 hu1 d
  have hsqv := xfun_sq_mul_Fz hv0 hv1 d
  have htu := xfun_mul_Fz_eq_tent hu0 hu1 d
  have htv := xfun_mul_Fz_eq_tent hv0 hv1 d
  linear_combination ((d : K) * (Fz v (d : ℤ) + 2)) * hsqu
    + ((d : K) * (Fz u (d : ℤ) + 2)) * hsqv
    + (-(2 * (d : K) * (xfun v * Fz v (d : ℤ))) - 8 * (d : K) * xfun v) * htu
    + (-(2 * (d : K) * tent u d) - 8 * (d : K) * xfun u) * htv

theorem crossSquare_absorb [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (M : ℕ) :
    (xCoeff (u * v) M + xCoeff (u * v⁻¹) M) * (xfun u - xfun v) ^ 2
        - 2 * (xfun u ^ 2 * xCoeff v M) - 2 * (xfun v ^ 2 * xCoeff u M)
        - 4 * (xfun u * xfun v * xCoeff u M) - 4 * (xfun u * xfun v * xCoeff v M)
      = (∑ d ∈ M.divisors, (d : K) *
            ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k)
              + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k)
              - 2 * (tent u d * tent v d)))
        + xfun u * (∑ d ∈ M.divisors, (d : K) ^ 3 * (Fz v (d : ℤ) + 2))
        + xfun v * (∑ d ∈ M.divisors, (d : K) ^ 3 * (Fz u (d : ℤ) + 2))
        - 8 * (xfun u * ∑ d ∈ M.divisors, (d : K) * tent v d)
        - 8 * (xfun v * ∑ d ∈ M.divisors, (d : K) * tent u d) := by
  calc (xCoeff (u * v) M + xCoeff (u * v⁻¹) M) * (xfun u - xfun v) ^ 2
        - 2 * (xfun u ^ 2 * xCoeff v M) - 2 * (xfun v ^ 2 * xCoeff u M)
        - 4 * (xfun u * xfun v * xCoeff u M) - 4 * (xfun u * xfun v * xCoeff v M)
      = ∑ d ∈ M.divisors,
          ((d : K) * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ))
              * (xfun u - xfun v) ^ 2
            - 2 * (xfun u ^ 2 * ((d : K) * Fz v (d : ℤ)))
            - 2 * (xfun v ^ 2 * ((d : K) * Fz u (d : ℤ)))
            - 4 * (xfun u * xfun v * ((d : K) * Fz u (d : ℤ)))
            - 4 * (xfun u * xfun v * ((d : K) * Fz v (d : ℤ)))) := by
        rw [xCoeff_mul_add_xCoeff_mul_inv hu0 hv0 M, xCoeff_eq_sum_mul_Fz u M,
          xCoeff_eq_sum_mul_Fz v M, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
          ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    _ = ∑ d ∈ M.divisors,
          ((d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k)
                + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k)
                - 2 * (tent u d * tent v d))
            + xfun u * ((d : K) ^ 3 * (Fz v (d : ℤ) + 2))
            + xfun v * ((d : K) ^ 3 * (Fz u (d : ℤ) + 2))
            - 8 * (xfun u * ((d : K) * tent v d))
            - 8 * (xfun v * ((d : K) * tent u d))) :=
        Finset.sum_congr rfl fun d _ => crossSquare_per_divisor_C2AssemblyS1 hu0 hv0 hu1 hv1 d
    _ = (∑ d ∈ M.divisors, (d : K) *
            ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k)
              + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k)
              - 2 * (tent u d * tent v d)))
        + xfun u * (∑ d ∈ M.divisors, (d : K) ^ 3 * (Fz v (d : ℤ) + 2))
        + xfun v * (∑ d ∈ M.divisors, (d : K) ^ 3 * (Fz u (d : ℤ) + 2))
        - 8 * (xfun u * ∑ d ∈ M.divisors, (d : K) * tent v d)
        - 8 * (xfun v * ∑ d ∈ M.divisors, (d : K) * tent u d) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

end SquareComplex

section CrossInterior

private theorem crossInterior_per_index_C2AssemblyS1 (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (a b : ℕ) :
    (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
        * (2 * ((xfun u - xfun v) * (xCoeff u b - xCoeff v b))
            + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                (fun i => xCoeffFull u i - xCoeffFull v i) b)
      = ((xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
            * (2 * ((∑ e ∈ b.divisors, (e : K) * tent u e)
                  + ∑ e ∈ b.divisors, (e : K) * tent v e)
              + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                  (fun i => xCoeffFull u i - xCoeffFull v i) b)
          - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d) * xCoeff v b)
          - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz u (d : ℤ) + 2) * tent v d) * xCoeff u b))
        - 4 * (xfun u * (xCoeff v a * xCoeff v b))
        - 4 * (xfun v * (xCoeff u a * xCoeff u b)) := by
  have h1u := xfun_mul_xCoeff_eq_sum_tent hu0 hu1 b
  have h1v := xfun_mul_xCoeff_eq_sum_tent hv0 hv1 b
  have h2u := xfun_mul_crossSum_left hu0 hv0 hu1 a
  have h2v := xfun_mul_crossSum_right hu0 hv0 hv1 a
  linear_combination (2 * (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)) * h1u
    + (2 * (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)) * h1v
    - (2 * xCoeff v b) * h2u - (2 * xCoeff u b) * h2v

theorem crossInterior_absorb (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (M : ℕ) :
    (∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
        * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a)))
            + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)))
      = (∑ a ∈ Finset.Ico 1 M,
            ((xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
                * (2 * ((∑ e ∈ (M - a).divisors, (e : K) * tent u e)
                      + ∑ e ∈ (M - a).divisors, (e : K) * tent v e)
                  + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                      (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))
              - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d)
                  * xCoeff v (M - a))
              - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz u (d : ℤ) + 2) * tent v d)
                  * xCoeff u (M - a))))
        - 4 * (xfun u * cauchyMulInt (xCoeffFull v) (xCoeffFull v) M)
        - 4 * (xfun v * cauchyMulInt (xCoeffFull u) (xCoeffFull u) M) := by
  have e1 : 4 * (xfun u * cauchyMulInt (xCoeffFull v) (xCoeffFull v) M)
      = ∑ a ∈ Finset.Ico 1 M, 4 * (xfun u * (xCoeff v a * xCoeff v (M - a))) := by
    rw [cauchyMulInt, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_Ico] at ha
    rw [xCoeffFull_of_pos v (show 0 < a by omega), xCoeffFull_of_pos v (show 0 < M - a by omega)]
  have e2 : 4 * (xfun v * cauchyMulInt (xCoeffFull u) (xCoeffFull u) M)
      = ∑ a ∈ Finset.Ico 1 M, 4 * (xfun v * (xCoeff u a * xCoeff u (M - a))) := by
    rw [cauchyMulInt, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_Ico] at ha
    rw [xCoeffFull_of_pos u (show 0 < a by omega), xCoeffFull_of_pos u (show 0 < M - a by omega)]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.Ico 1 M) =>
    crossInterior_per_index_C2AssemblyS1 hu0 hv0 hu1 hv1 a (M - a)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, e1, e2]

end CrossInterior

section Assembly

theorem addDefectSumCoeff_eq_absorbed [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M) :
    addDefectSumCoeff u v M
      = (∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) *
            ((u ^ x.1 - v ^ x.1) * (u ^ x.2.2.1 - v ^ x.2.2.1)
                * (u * v * (∑ i ∈ Finset.range x.1, (u * v) ^ i)
                    * (∑ i ∈ Finset.range x.2.2.1, (u * v) ^ i)
                    * ((u * v) ^ x.1)⁻¹ * ((u * v) ^ x.2.2.1)⁻¹)
              + (u ^ x.1 - (v ^ x.1)⁻¹) * (u ^ x.2.2.1 - (v ^ x.2.2.1)⁻¹)
                  * (u * v⁻¹ * (∑ i ∈ Finset.range x.1, (u * v⁻¹) ^ i)
                      * (∑ i ∈ Finset.range x.2.2.1, (u * v⁻¹) ^ i)
                      * ((u * v⁻¹) ^ x.1)⁻¹ * ((u * v⁻¹) ^ x.2.2.1)⁻¹)))
        - 2 * ∑ d ∈ M.divisors, (d : K) *
            ((∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j))
              - ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j))
        + (∑ d ∈ M.divisors, (d : K) *
            ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k)
              + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k)
              - 2 * (tent u d * tent v d)))
        + (∑ a ∈ Finset.Ico 1 M,
            ((xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
                * (2 * ((∑ e ∈ (M - a).divisors, (e : K) * tent u e)
                      + ∑ e ∈ (M - a).divisors, (e : K) * tent v e)
                  + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                      (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))
              - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d)
                  * xCoeff v (M - a))
              - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz u (d : ℤ) + 2) * tent v d)
                  * xCoeff u (M - a))))
        - 4 * ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1
        - 4 * ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1)
        - 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M
        - 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M
        - cauchyMulInt (xCoeffFull u) (xCoeffFull v) M
        - 2 * cauchyMulInt a₄Coeff (xCoeffFull u) M
        - 2 * cauchyMulInt a₄Coeff (xCoeffFull v) M
        - 4 * a₆Coeff M := by

  have htent2 := xfun_add_mul_xfun_sub_mul_xCoeff_sub_tentForm hu0 hv0 hu1 hv1 huvm huvd M
  have hC := crossSquare_absorb hu0 hv0 hu1 hv1 M
  have hD := crossInterior_absorb hu0 hv0 hu1 hv1 M
  have hbinU := sameVarPole_discharge (v := v) hv0 M
  have hbinV := sameVarPole_discharge (v := u) hu0 M

  have hDD : cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
      (fun i => xCoeffFull u i - xCoeffFull v i) M
      = ∑ x ∈ Sols M, (xDivTerm u x.1 - xDivTerm v x.1)
          * (xDivTerm u x.2.2.1 - xDivTerm v x.2.2.1) :=
    cauchyMulInt_eq_sum_Sols (f := fun a => xDivTerm u a - xDivTerm v a)
      (g := fun a => xDivTerm u a - xDivTerm v a) M
      (fun i hi => by
        show xCoeffFull u i - xCoeffFull v i
            = ∑ a ∈ i.divisors, (xDivTerm u a - xDivTerm v a)
        rw [xCoeffFull_of_pos u hi, xCoeffFull_of_pos v hi, xCoeff, xCoeff,
          ← Finset.sum_sub_distrib])
      (fun i hi => by
        show xCoeffFull u i - xCoeffFull v i
            = ∑ a ∈ i.divisors, (xDivTerm u a - xDivTerm v a)
        rw [xCoeffFull_of_pos u hi, xCoeffFull_of_pos v hi, xCoeff, xCoeff,
          ← Finset.sum_sub_distrib])

  have hA : (xfun (u * v) + xfun (u * v⁻¹))
      * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
          (fun i => xCoeffFull u i - xCoeffFull v i) M
      = ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) *
          ((u ^ x.1 - v ^ x.1) * (u ^ x.2.2.1 - v ^ x.2.2.1)
              * (u * v * (∑ i ∈ Finset.range x.1, (u * v) ^ i)
                  * (∑ i ∈ Finset.range x.2.2.1, (u * v) ^ i)
                  * ((u * v) ^ x.1)⁻¹ * ((u * v) ^ x.2.2.1)⁻¹)
            + (u ^ x.1 - (v ^ x.1)⁻¹) * (u ^ x.2.2.1 - (v ^ x.2.2.1)⁻¹)
                * (u * v⁻¹ * (∑ i ∈ Finset.range x.1, (u * v⁻¹) ^ i)
                    * (∑ i ∈ Finset.range x.2.2.1, (u * v⁻¹) ^ i)
                    * ((u * v⁻¹) ^ x.1)⁻¹ * ((u * v⁻¹) ^ x.2.2.1)⁻¹)) := by
    rw [hDD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hc1 := xfun_mul_mul_Fz_sub_mul_Fz_sub hu0 hv0 huvm x.1 x.2.2.1
    have hc2 := xfun_mul_inv_mul_Fz_sub_mul_Fz_sub hu0 hv0 huvd x.1 x.2.2.1
    simp only [xDivTerm_eq_mul_Fz]
    linear_combination ((x.1 : K) * (x.2.2.1 : K)) * hc1 + ((x.1 : K) * (x.2.2.1 : K)) * hc2

  have hPQ : cauchyMulInt (xCoeffFull u) (xCoeffFull v) M
      = ∑ x ∈ Sols M, xDivTerm u x.1 * xDivTerm v x.2.2.1 :=
    cauchyMulInt_eq_sum_Sols (f := xDivTerm u) (g := xDivTerm v) M
      (fun i hi => by
        show xCoeffFull u i = ∑ a ∈ i.divisors, xDivTerm u a
        rw [xCoeffFull_of_pos u hi, xCoeff])
      (fun i hi => by
        show xCoeffFull v i = ∑ a ∈ i.divisors, xDivTerm v a
        rw [xCoeffFull_of_pos v hi, xCoeff])

  have hE1 : xfun u * cauchyMulInt (xCoeffFull u) (xCoeffFull v) M
      = ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1 := by
    rw [hPQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have ht := xfun_mul_Fz_eq_tent hu0 hu1 x.1
    rw [xDivTerm_eq_mul_Fz u x.1]
    linear_combination ((x.1 : K) * xDivTerm v x.2.2.1) * ht
  have hE2 : xfun v * cauchyMulInt (xCoeffFull u) (xCoeffFull v) M
      = ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1) := by
    rw [hPQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have ht := xfun_mul_Fz_eq_tent hv0 hv1 x.2.2.1
    rw [xDivTerm_eq_mul_Fz v x.2.2.1]
    linear_combination (xDivTerm u x.1 * (x.2.2.1 : K)) * ht

  rw [addDefectSumCoeff_eq_boundary_add_int u v hM]
  linear_combination hA + 2 * htent2 + hC + hD - 4 * hE1 - 4 * hE2
    + xfun u * hbinU + xfun v * hbinV

end Assembly

end TateCurve

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz Fz_natCast Fz_mul_Fz xDivTerm_eq_mul_Fz a₆Coeff_of_pos tent xfun_mul_Fz_eq_tent cauchyMulInt_a4x_eq_neg_sum_Sols tent_eq_sq_add_sum_Ico add_le_of_mem_Sols cauchyMul xCoeffFull xCoeffFull_succ a₄Coeff a₄Coeff_succ a₆Coeff xfun yfun xfun_inv pointX pointY term b b_mul_twelve a₄ a₆ curve xDivTerm xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

open Finset

variable {K : Type*} [NontriviallyNormedField K]

theorem six_mul_sum_range_sq_cast (d : ℕ) :
    (6 : K) * ∑ k ∈ Finset.range d, (k : K) ^ 2
      = 2 * (d : K) ^ 3 - 3 * (d : K) ^ 2 + (d : K) := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem four_mul_sum_range_cube_cast (d : ℕ) :
    (4 : K) * ∑ k ∈ Finset.range d, (k : K) ^ 3 = ((d : K) ^ 2 - (d : K)) ^ 2 := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem twelve_mul_sum_Ico_sub_mul_sq_cast (d : ℕ) :
    (12 : K) * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2
      = (d : K) ^ 4 - (d : K) ^ 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp

  have h0 : ∑ k ∈ Finset.range d, ((d - k : ℕ) : K) * (k : K) ^ 2
      = ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2 := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hd]
    simp
  rw [← h0]

  have h1 : ∑ k ∈ Finset.range d, ((d - k : ℕ) : K) * (k : K) ^ 2
      = (d : K) * (∑ k ∈ Finset.range d, (k : K) ^ 2)
        - ∑ k ∈ Finset.range d, (k : K) ^ 3 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Nat.cast_sub (Finset.mem_range.mp hk).le]
    ring
  rw [h1]
  have h2 := six_mul_sum_range_sq_cast (K := K) d
  have h3 := four_mul_sum_range_cube_cast (K := K) d
  linear_combination (2 * (d : K)) * h2 - 3 * h3

theorem sum_sq_mul_sq_pairing (d : ℕ) (hd : 0 < d) :
    (∑ j ∈ Finset.Icc 1 d, (j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2)
        - ∑ j ∈ Finset.range d, (j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2
      = 4 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2 + (d : K) ^ 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_pos hd).symm⟩
  have hIco : Finset.Ico 1 (e + 1) = Finset.Icc 1 e := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega

  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ e + 1),
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < e + 1)]
  simp only [zero_add]
  rw [hIco]

  have hsum : (∑ j ∈ Finset.Icc 1 e, (j : K) ^ 2 * ((e + 1 + 1 - j : ℕ) : K) ^ 2)
      = (∑ j ∈ Finset.Icc 1 e, (j : K) ^ 2 * ((e + 1 - 1 - j : ℕ) : K) ^ 2)
        + 4 * ∑ j ∈ Finset.Icc 1 e, ((e + 1 - j : ℕ) : K) * (j : K) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hje : j ≤ e := (Finset.mem_Icc.mp hj).2
    rw [show e + 1 + 1 - j = (e - j) + 2 by omega, show e + 1 - 1 - j = e - j by omega,
      show e + 1 - j = (e - j) + 1 by omega]
    push_cast
    ring
  rw [hsum, show e + 1 + 1 - (e + 1) = 1 by omega]
  push_cast
  ring

theorem constantBin_perDivisor [CharZero K] {d : ℕ} (hd : 0 < d) :
    -2 * ((d : K) *
        ((∑ j ∈ Finset.Icc 1 d, (j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2)
          - ∑ j ∈ Finset.range d, (j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2))
      + (d : K) *
          (2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2
            + 2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2
            - 2 * ((d : K) ^ 2 * (d : K) ^ 2))
      + 4 * (b d : K) = 0 := by
  have hAB := sum_sq_mul_sq_pairing (K := K) d hd
  have hS := twelve_mul_sum_Ico_sub_mul_sq_cast (K := K) d
  have hb : ((b d * 12 : ℕ) : K) = ((5 * d ^ 3 + 7 * d ^ 5 : ℕ) : K) :=
    congrArg (Nat.cast (R := K)) (b_mul_twelve d)
  push_cast at hb
  linear_combination (-2 * (d : K)) * hAB + (-(d : K) / 3) * hS + (1 / 3 : K) * hb

theorem constantBin_eq_zero [CharZero K] {M : ℕ} (hM : 0 < M) :
    -2 * ∑ d ∈ M.divisors, (d : K) *
        ((∑ j ∈ Finset.Icc 1 d, (j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2)
          - ∑ j ∈ Finset.range d, (j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2)
      + ∑ d ∈ M.divisors, (d : K) *
          (2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2
            + 2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2
            - 2 * ((d : K) ^ 2 * (d : K) ^ 2))
      - 4 * a₆Coeff M = 0 := by
  have h : ∑ d ∈ M.divisors,
      ((-2 : K) * ((d : K) *
          ((∑ j ∈ Finset.Icc 1 d, (j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2)
            - ∑ j ∈ Finset.range d, (j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2))
        + ((d : K) *
            (2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2
              + 2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2
              - 2 * ((d : K) ^ 2 * (d : K) ^ 2))
          + (4 : K) * (b d : K))) = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    have hpd := constantBin_perDivisor (K := K) (Nat.pos_of_mem_divisors hd)
    linear_combination hpd
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  rw [a₆Coeff_of_pos hM]
  linear_combination h

@[scoped simp] theorem xDivTerm_one_left (d : ℕ) : xDivTerm (1 : K) d = 0 := by
  norm_num [xDivTerm]

@[scoped simp] theorem xCoeff_one_left (N : ℕ) : xCoeff (1 : K) N = 0 := by
  simp [xCoeff]

theorem xCoeffFull_one_left_of_pos {N : ℕ} (hN : 0 < N) : xCoeffFull (1 : K) N = 0 := by
  rw [xCoeffFull_of_pos _ hN, xCoeff_one_left]

@[scoped simp] theorem Fz_one_left (a : ℤ) : Fz (1 : K) a = 0 := by
  norm_num [Fz]

@[scoped simp] theorem tent_one_left (m : ℕ) : tent (1 : K) m = (m : K) ^ 2 := by
  simp [tent]

theorem cauchyMulInt_eq_zero_of_left {c d : ℕ → K} (hc : ∀ i, 0 < i → c i = 0) (N : ℕ) :
    cauchyMulInt c d N = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hc i (Finset.mem_Ico.mp hi).1, zero_mul]

theorem cauchyMulInt_eq_zero_of_right {c d : ℕ → K} (hd : ∀ i, 0 < i → d i = 0) (N : ℕ) :
    cauchyMulInt c d N = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' := Finset.mem_Ico.mp hi
  rw [hd (N - i) (by omega), mul_zero]

theorem cauchyMulIntTriple_eq_zero_of_left {c d e : ℕ → K} (hc : ∀ i, 0 < i → c i = 0)
    (N : ℕ) : cauchyMulIntTriple c d e N = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hc i (Finset.mem_Ico.mp hi).1, zero_mul]

theorem cauchyMulIntTriple_eq_zero_of_right {c d e : ℕ → K} (he : ∀ i, 0 < i → e i = 0)
    (N : ℕ) : cauchyMulIntTriple c d e N = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [cauchyMulInt_eq_zero_of_right he, mul_zero]

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz Fz_natCast Fz_mul_Fz xDivTerm_eq_mul_Fz a₆Coeff_of_pos tent xfun_mul_Fz_eq_tent cauchyMulInt_a4x_eq_neg_sum_Sols tent_eq_sq_add_sum_Ico add_le_of_mem_Sols cauchyMul xCoeffFull xCoeffFull_succ a₄Coeff a₄Coeff_succ a₆Coeff xfun yfun xfun_inv pointX pointY term b b_mul_twelve a₄ a₆ curve xDivTerm xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] {u v : K}

section CrossPairExpansion

private noncomputable def crossFamOne_C2RowCollapse (u₀ v₀ : K) (a c i i' : ℕ) : K :=
  u₀ ^ (i + i' + 1)
    * (v₀ ^ (a + c) * (v₀ ^ (i + i' + 1))⁻¹ + v₀ ^ (i + i' + 1) * (v₀ ^ (a + c))⁻¹)

private noncomputable def crossFamTwo_C2RowCollapse (u₀ v₀ : K) (a c i i' : ℕ) : K :=
  u₀ ^ (i + i' + 1) * (u₀ ^ c)⁻¹
    * (v₀ ^ (i + i' + 1) * (v₀ ^ a)⁻¹ + v₀ ^ a * (v₀ ^ (i + i' + 1))⁻¹)

private noncomputable def crossFamThree_C2RowCollapse (u₀ v₀ : K) (a c i i' : ℕ) : K :=
  u₀ ^ (i + i' + 1) * (u₀ ^ a)⁻¹
    * (v₀ ^ (i + i' + 1) * (v₀ ^ c)⁻¹ + v₀ ^ c * (v₀ ^ (i + i' + 1))⁻¹)

private noncomputable def crossFamFour_C2RowCollapse (u₀ v₀ : K) (a c i i' : ℕ) : K :=
  u₀ ^ (i + i' + 1) * (u₀ ^ (a + c))⁻¹ * (v₀ ^ (i + i' + 1) + (v₀ ^ (i + i' + 1))⁻¹)

set_option maxHeartbeats 3200000 in

private theorem crossPair_summand_C2RowCollapse (hu0 : u ≠ 0) (hv0 : v ≠ 0) (a c i i' : ℕ) :
    (u ^ a - v ^ a) * (u ^ c - v ^ c)
        * (u * v * ((u * v) ^ a)⁻¹ * ((u * v) ^ c)⁻¹) * ((u * v) ^ i * (u * v) ^ i')
      + (u ^ a - (v ^ a)⁻¹) * (u ^ c - (v ^ c)⁻¹)
          * (u * v⁻¹ * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ c)⁻¹)
          * ((u * v⁻¹) ^ i * (u * v⁻¹) ^ i')
    = crossFamOne_C2RowCollapse u v a c i i' - crossFamTwo_C2RowCollapse u v a c i i' - crossFamThree_C2RowCollapse u v a c i i'
        + crossFamFour_C2RowCollapse u v a c i i' := by
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
  simp only [crossFamOne_C2RowCollapse, crossFamTwo_C2RowCollapse, crossFamThree_C2RowCollapse, crossFamFour_C2RowCollapse, hppu, hppv, hpau, hpav,
    mul_pow, inv_pow, mul_inv]
  field_simp
  ring

private theorem crossFam_pair_one_C2RowCollapse (hu0 : u ≠ 0) (hv0 : v ≠ 0) {a c i i' : ℕ}
    (hi : i < a) (hi' : i' < c) :
    crossFamOne_C2RowCollapse u v a c i i' + crossFamFour_C2RowCollapse u v a c (a - 1 - i) (c - 1 - i')
      = (Fz u ((i : ℤ) + i' + 1) + 2) * (Fz v ((a : ℤ) + c - 1 - i - i') + 2) := by
  have hupow : u ^ (a + c) = u ^ ((a - 1 - i) + (c - 1 - i') + 1) * u ^ (i + i' + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hvpow : v ^ (a + c) = v ^ ((a - 1 - i) + (c - 1 - i') + 1) * v ^ (i + i' + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hum : u ^ ((a - 1 - i) + (c - 1 - i') + 1) ≠ 0 := pow_ne_zero _ hu0
  have hup : u ^ (i + i' + 1) ≠ 0 := pow_ne_zero _ hu0
  have hvm : v ^ ((a - 1 - i) + (c - 1 - i') + 1) ≠ 0 := pow_ne_zero _ hv0
  have hvp : v ^ (i + i' + 1) ≠ 0 := pow_ne_zero _ hv0

  have hFu : Fz u ((i : ℤ) + i' + 1) + 2 = u ^ (i + i' + 1) + (u ^ (i + i' + 1))⁻¹ := by
    have hcast : ((i : ℤ) + i' + 1) = ((i + i' + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Fz_natCast, inv_pow]
    ring
  have hFv : Fz v ((a : ℤ) + c - 1 - i - i') + 2
      = v ^ ((a - 1 - i) + (c - 1 - i') + 1) + (v ^ ((a - 1 - i) + (c - 1 - i') + 1))⁻¹ := by
    have hcast : ((a : ℤ) + c - 1 - i - i') = (((a - 1 - i) + (c - 1 - i') + 1 : ℕ) : ℤ) := by
      omega
    rw [hcast, Fz_natCast, inv_pow]
    ring
  rw [hFu, hFv]
  simp only [crossFamOne_C2RowCollapse, crossFamFour_C2RowCollapse, hupow, hvpow, mul_inv]
  field_simp

private theorem crossFam_pair_two_C2RowCollapse (hu0 : u ≠ 0) (hv0 : v ≠ 0) {a c i i' : ℕ}
    (hi : i < a) (hi' : i' < c) :
    crossFamTwo_C2RowCollapse u v a c i i' + crossFamThree_C2RowCollapse u v a c (a - 1 - i) (c - 1 - i')
      = (Fz u ((i : ℤ) + i' + 1 - c) + 2) * (Fz v ((i : ℤ) + i' + 1 - a) + 2) := by
  have hm : ((a - 1 - i) + (c - 1 - i') + 1) + (i + i' + 1) = a + c := by omega
  have hua : u ^ a ≠ 0 := pow_ne_zero _ hu0
  have huc : u ^ c ≠ 0 := pow_ne_zero _ hu0
  have hup : u ^ (i + i' + 1) ≠ 0 := pow_ne_zero _ hu0
  have hum : u ^ ((a - 1 - i) + (c - 1 - i') + 1) ≠ 0 := pow_ne_zero _ hu0
  have hva : v ^ a ≠ 0 := pow_ne_zero _ hv0
  have hvc : v ^ c ≠ 0 := pow_ne_zero _ hv0
  have hvp : v ^ (i + i' + 1) ≠ 0 := pow_ne_zero _ hv0
  have hvm : v ^ ((a - 1 - i) + (c - 1 - i') + 1) ≠ 0 := pow_ne_zero _ hv0

  have hFu : Fz u ((i : ℤ) + i' + 1 - c) + 2
      = u ^ (i + i' + 1) * (u ^ c)⁻¹ + u ^ c * (u ^ (i + i' + 1))⁻¹ := by
    have h1 : ((i : ℤ) + i' + 1 - c) = ((i + i' + 1 : ℕ) : ℤ) - (c : ℤ) := by push_cast; ring
    have h2 : -(((i + i' + 1 : ℕ) : ℤ) - (c : ℤ)) = (c : ℤ) - ((i + i' + 1 : ℕ) : ℤ) := by ring
    simp only [Fz]
    rw [h1, h2, zpow_sub₀ hu0, zpow_sub₀ hu0]
    simp only [zpow_natCast]
    ring
  have hFv : Fz v ((i : ℤ) + i' + 1 - a) + 2
      = v ^ (i + i' + 1) * (v ^ a)⁻¹ + v ^ a * (v ^ (i + i' + 1))⁻¹ := by
    have h1 : ((i : ℤ) + i' + 1 - a) = ((i + i' + 1 : ℕ) : ℤ) - (a : ℤ) := by push_cast; ring
    have h2 : -(((i + i' + 1 : ℕ) : ℤ) - (a : ℤ)) = (a : ℤ) - ((i + i' + 1 : ℕ) : ℤ) := by ring
    simp only [Fz]
    rw [h1, h2, zpow_sub₀ hv0, zpow_sub₀ hv0]
    simp only [zpow_natCast]
    ring
  rw [hFu, hFv]

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
  simp only [crossFamTwo_C2RowCollapse, crossFamThree_C2RowCollapse]
  rw [hum_eq, hvm_eq]
  field_simp
  ring

private theorem crossPair_side_distrib_C2RowCollapse (P w : K) (a c : ℕ) :
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

private theorem crossPair_perterm_C2RowCollapse (hu0 : u ≠ 0) (hv0 : v ≠ 0) {a c i i' : ℕ}
    (hi : i < a) (hi' : i' < c) :
    (u ^ a - v ^ a) * (u ^ c - v ^ c)
        * (u * v * ((u * v) ^ a)⁻¹ * ((u * v) ^ c)⁻¹) * ((u * v) ^ i * (u * v) ^ i')
      + (u ^ a - (v ^ a)⁻¹) * (u ^ c - (v ^ c)⁻¹)
          * (u * v⁻¹ * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ c)⁻¹)
          * ((u * v⁻¹) ^ i * (u * v⁻¹) ^ i')
    = ((Fz u ((i : ℤ) + i' + 1) + 2) * (Fz v ((a : ℤ) + c - 1 - i - i') + 2)
        - (Fz u ((i : ℤ) + i' + 1 - c) + 2) * (Fz v ((i : ℤ) + i' + 1 - a) + 2))
      + (crossFamFour_C2RowCollapse u v a c i i' - crossFamFour_C2RowCollapse u v a c (a - 1 - i) (c - 1 - i'))
      - (crossFamThree_C2RowCollapse u v a c i i' - crossFamThree_C2RowCollapse u v a c (a - 1 - i) (c - 1 - i')) := by
  rw [crossPair_summand_C2RowCollapse hu0 hv0 a c i i', ← crossFam_pair_one_C2RowCollapse hu0 hv0 hi hi',
    ← crossFam_pair_two_C2RowCollapse hu0 hv0 hi hi']
  ring

private theorem crossFamFour_reflect_C2RowCollapse (a c : ℕ) :
    (∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c,
        crossFamFour_C2RowCollapse u v a c (a - 1 - i) (c - 1 - i'))
      = ∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c, crossFamFour_C2RowCollapse u v a c i i' := by
  rw [← Finset.sum_range_reflect
    (fun i => ∑ i' ∈ Finset.range c, crossFamFour_C2RowCollapse u v a c i i') a]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_range_reflect (fun i' => crossFamFour_C2RowCollapse u v a c (a - 1 - i) i') c

private theorem crossFamThree_reflect_C2RowCollapse (a c : ℕ) :
    (∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c,
        crossFamThree_C2RowCollapse u v a c (a - 1 - i) (c - 1 - i'))
      = ∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c, crossFamThree_C2RowCollapse u v a c i i' := by
  rw [← Finset.sum_range_reflect
    (fun i => ∑ i' ∈ Finset.range c, crossFamThree_C2RowCollapse u v a c i i') a]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_range_reflect (fun i' => crossFamThree_C2RowCollapse u v a c (a - 1 - i) i') c

theorem crossPair_expansion (hu0 : u ≠ 0) (hv0 : v ≠ 0) (a c : ℕ) :
    (u ^ a - v ^ a) * (u ^ c - v ^ c)
        * (u * v * (∑ i ∈ Finset.range a, (u * v) ^ i) * (∑ i ∈ Finset.range c, (u * v) ^ i)
            * ((u * v) ^ a)⁻¹ * ((u * v) ^ c)⁻¹)
      + (u ^ a - (v ^ a)⁻¹) * (u ^ c - (v ^ c)⁻¹)
          * (u * v⁻¹ * (∑ i ∈ Finset.range a, (u * v⁻¹) ^ i)
              * (∑ i ∈ Finset.range c, (u * v⁻¹) ^ i)
              * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ c)⁻¹)
    = ∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c,
        ((Fz u ((i : ℤ) + i' + 1) + 2) * (Fz v ((a : ℤ) + c - 1 - i - i') + 2)
          - (Fz u ((i : ℤ) + i' + 1 - c) + 2) * (Fz v ((i : ℤ) + i' + 1 - a) + 2)) := by

  have hdist : (u ^ a - v ^ a) * (u ^ c - v ^ c)
        * (u * v * (∑ i ∈ Finset.range a, (u * v) ^ i) * (∑ i ∈ Finset.range c, (u * v) ^ i)
            * ((u * v) ^ a)⁻¹ * ((u * v) ^ c)⁻¹)
      + (u ^ a - (v ^ a)⁻¹) * (u ^ c - (v ^ c)⁻¹)
          * (u * v⁻¹ * (∑ i ∈ Finset.range a, (u * v⁻¹) ^ i)
              * (∑ i ∈ Finset.range c, (u * v⁻¹) ^ i)
              * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ c)⁻¹)
      = ∑ i ∈ Finset.range a, ∑ i' ∈ Finset.range c,
          ((u ^ a - v ^ a) * (u ^ c - v ^ c)
              * (u * v * ((u * v) ^ a)⁻¹ * ((u * v) ^ c)⁻¹) * ((u * v) ^ i * (u * v) ^ i')
            + (u ^ a - (v ^ a)⁻¹) * (u ^ c - (v ^ c)⁻¹)
                * (u * v⁻¹ * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ c)⁻¹)
                * ((u * v⁻¹) ^ i * (u * v⁻¹) ^ i')) := by
    rw [crossPair_side_distrib_C2RowCollapse ((u ^ a - v ^ a) * (u ^ c - v ^ c)) (u * v) a c,
      crossPair_side_distrib_C2RowCollapse ((u ^ a - (v ^ a)⁻¹) * (u ^ c - (v ^ c)⁻¹)) (u * v⁻¹) a c,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_add_distrib).symm
  rw [hdist]

  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun i' hi' =>
    crossPair_perterm_C2RowCollapse hu0 hv0 (Finset.mem_range.mp hi) (Finset.mem_range.mp hi')]

  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [crossFamFour_reflect_C2RowCollapse, crossFamThree_reflect_C2RowCollapse]
  ring

end CrossPairExpansion
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz Fz_natCast Fz_mul_Fz xDivTerm_eq_mul_Fz a₆Coeff_of_pos tent xfun_mul_Fz_eq_tent cauchyMulInt_a4x_eq_neg_sum_Sols tent_eq_sq_add_sum_Ico add_le_of_mem_Sols cauchyMul xCoeffFull xCoeffFull_succ a₄Coeff a₄Coeff_succ a₆Coeff xfun yfun xfun_inv pointX pointY term b b_mul_twelve a₄ a₆ curve xDivTerm xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section MixedConvolutions

theorem cauchyMulInt_x_x_eq_sum_Sols_Fz (u v : K) (M : ℕ) :
    cauchyMulInt (xCoeffFull u) (xCoeffFull v) M
      = ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * Fz u (x.1 : ℤ) * Fz v (x.2.2.1 : ℤ) := by
  rw [cauchyMulInt_eq_sum_Sols (f := xDivTerm u) (g := xDivTerm v) M
    (fun i hi => by rw [xCoeffFull_of_pos u hi, xCoeff])
    (fun i hi => by rw [xCoeffFull_of_pos v hi, xCoeff])]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz]
  ring

theorem cauchyMulInt_a₄_x_eq_sum_Sols_Fz (u : K) (M : ℕ) :
    cauchyMulInt a₄Coeff (xCoeffFull u) M
      = -(∑ x ∈ Sols M, ((5 * x.1 ^ 3 : ℕ) : K) * ((x.2.2.1 : K) * Fz u (x.2.2.1 : ℤ))) := by
  rw [cauchyMulInt_a4x_eq_neg_sum_Sols]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by rw [xDivTerm_eq_mul_Fz]

end MixedConvolutions
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

section Triples

theorem cauchyMulIntTriple_xxv_eq_sum_Fz (hu0 : u ≠ 0) (v : K) (M : ℕ) :
    cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M
      = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i),
          (d : K) * (x.1 : K) * (x.2.2.1 : K)
            * (Fz u ((d : ℤ) + (x.1 : ℤ)) + Fz u ((d : ℤ) - (x.1 : ℤ))
                - 2 * Fz u (d : ℤ) - 2 * Fz u (x.1 : ℤ))
            * Fz v (x.2.2.1 : ℤ) := by
  rw [cauchyMulIntTriple]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  rw [xCoeffFull_of_pos u (by omega), xCoeff,
    cauchyMulInt_eq_sum_Sols (f := xDivTerm u) (g := xDivTerm v) (M - i)
      (fun j hj => by rw [xCoeffFull_of_pos u hj, xCoeff])
      (fun j hj => by rw [xCoeffFull_of_pos v hj, xCoeff]),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz]
  have hprod := Fz_mul_Fz hu0 (d : ℤ) (x.1 : ℤ)
  linear_combination ((d : K) * (x.1 : K) * (x.2.2.1 : K) * Fz v (x.2.2.1 : ℤ)) * hprod

theorem cauchyMulIntTriple_xvv_eq_sum_Fz (u : K) (hv0 : v ≠ 0) (M : ℕ) :
    cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M
      = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i),
          (d : K) * (x.1 : K) * (x.2.2.1 : K) * Fz u (d : ℤ)
            * (Fz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + Fz v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
                - 2 * Fz v (x.1 : ℤ) - 2 * Fz v (x.2.2.1 : ℤ)) := by
  rw [cauchyMulIntTriple]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  rw [xCoeffFull_of_pos u (by omega), xCoeff,
    cauchyMulInt_eq_sum_Sols (f := xDivTerm v) (g := xDivTerm v) (M - i)
      (fun j hj => by rw [xCoeffFull_of_pos v hj, xCoeff])
      (fun j hj => by rw [xCoeffFull_of_pos v hj, xCoeff]),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz]
  have hprod := Fz_mul_Fz hv0 (x.1 : ℤ) (x.2.2.1 : ℤ)
  linear_combination ((d : K) * (x.1 : K) * (x.2.2.1 : K) * Fz u (d : ℤ)) * hprod

end Triples
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

section TentRows

theorem sum_Sols_tent_xDivTerm_eq_Fz [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (v : K)
    (M : ℕ) :
    ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1
      = (∑ x ∈ Sols M, (x.1 : K) ^ 3 * (x.2.2.1 : K) * Fz v (x.2.2.1 : ℤ))
        + ∑ x ∈ Sols M, ∑ j ∈ Finset.Ico 1 x.1,
            (x.1 : K) * ((x.1 - j : ℕ) : K) * (x.2.2.1 : K)
              * Fz u (j : ℤ) * Fz v (x.2.2.1 : ℤ) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hS : (x.1 : K) * (∑ j ∈ Finset.Ico 1 x.1, ((x.1 - j : ℕ) : K) * Fz u (j : ℤ))
        * ((x.2.2.1 : K) * Fz v (x.2.2.1 : ℤ))
      = ∑ j ∈ Finset.Ico 1 x.1, (x.1 : K) * ((x.1 - j : ℕ) : K) * (x.2.2.1 : K)
          * Fz u (j : ℤ) * Fz v (x.2.2.1 : ℤ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [tent_eq_sq_add_sum_Ico hu0 hu1 x.1, xDivTerm_eq_mul_Fz]
  linear_combination hS

theorem sum_Sols_xDivTerm_tent_eq_Fz [CharZero K] (u : K) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ) :
    ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1)
      = (∑ x ∈ Sols M, (x.2.2.1 : K) ^ 3 * (x.1 : K) * Fz u (x.1 : ℤ))
        + ∑ x ∈ Sols M, ∑ j ∈ Finset.Ico 1 x.2.2.1,
            (x.2.2.1 : K) * ((x.2.2.1 - j : ℕ) : K) * (x.1 : K)
              * Fz u (x.1 : ℤ) * Fz v (j : ℤ) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hS : ((x.1 : K) * Fz u (x.1 : ℤ))
        * ((x.2.2.1 : K) * (∑ j ∈ Finset.Ico 1 x.2.2.1, ((x.2.2.1 - j : ℕ) : K) * Fz v (j : ℤ)))
      = ∑ j ∈ Finset.Ico 1 x.2.2.1, (x.2.2.1 : K) * ((x.2.2.1 - j : ℕ) : K) * (x.1 : K)
          * Fz u (x.1 : ℤ) * Fz v (j : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [tent_eq_sq_add_sum_Ico hv0 hv1 x.2.2.1, xDivTerm_eq_mul_Fz]
  linear_combination hS

end TentRows
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz Fz_natCast Fz_mul_Fz xDivTerm_eq_mul_Fz a₆Coeff_of_pos tent xfun_mul_Fz_eq_tent cauchyMulInt_a4x_eq_neg_sum_Sols tent_eq_sq_add_sum_Ico add_le_of_mem_Sols cauchyMul xCoeffFull xCoeffFull_succ a₄Coeff a₄Coeff_succ a₆Coeff xfun yfun xfun_inv pointX pointY term b b_mul_twelve a₄ a₆ curve xDivTerm xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section TentProducts

theorem tent_mul_tent_eq [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (j m : ℕ) :
    tent v j * tent u m
      = (j : K) ^ 2 * (m : K) ^ 2
        + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 m, ((m - l : ℕ) : K) * Fz u (l : ℤ))
        + (m : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ))
        + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 m,
            ((j - l : ℕ) : K) * ((m - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ) := by
  rw [tent_eq_sq_add_sum_Ico hv0 hv1 j, tent_eq_sq_add_sum_Ico hu0 hu1 m]
  have hsum : (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ))
        * (∑ l' ∈ Finset.Ico 1 m, ((m - l' : ℕ) : K) * Fz u (l' : ℤ))
      = ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 m,
          ((j - l : ℕ) : K) * ((m - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l' _ => by ring
  linear_combination hsum

theorem Fz_mul_tent_eq [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (a : ℤ) (e : ℕ) :
    Fz u a * tent u e
      = (e : K) ^ 2 * Fz u a
        + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K)
            * (Fz u (a + (l : ℤ)) + Fz u (a - (l : ℤ)) - 2 * Fz u a - 2 * Fz u (l : ℤ)) := by
  rw [tent_eq_sq_add_sum_Ico hu0 hu1 e]
  have hsum : Fz u a * (∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz u (l : ℤ))
      = ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K)
          * (Fz u (a + (l : ℤ)) + Fz u (a - (l : ℤ)) - 2 * Fz u a - 2 * Fz u (l : ℤ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h := Fz_mul_Fz hu0 a (l : ℤ)
    linear_combination ((e - l : ℕ) : K) * h
  linear_combination hsum

end TentProducts
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

section CrossReadings

theorem crossPair_term_expand (u v : K) (α β γ δ : ℤ) :
    (Fz u α + 2) * (Fz v β + 2) - (Fz u γ + 2) * (Fz v δ + 2)
      = Fz u α * Fz v β - Fz u γ * Fz v δ + 2 * (Fz u α - Fz u γ) + 2 * (Fz v β - Fz v δ) := by
  ring

theorem cauchyMulInt_diff_diff_eq_sum_Fz (hu0 : u ≠ 0) (hv0 : v ≠ 0) (N : ℕ) :
    cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
        (fun i => xCoeffFull u i - xCoeffFull v i) N
      = ∑ x ∈ Sols N, (x.1 : K) * (x.2.2.1 : K) *
          (Fz u ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + Fz u ((x.1 : ℤ) - (x.2.2.1 : ℤ))
              - 2 * Fz u (x.1 : ℤ) - 2 * Fz u (x.2.2.1 : ℤ)
            + Fz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + Fz v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
              - 2 * Fz v (x.1 : ℤ) - 2 * Fz v (x.2.2.1 : ℤ)
            - Fz u (x.1 : ℤ) * Fz v (x.2.2.1 : ℤ) - Fz u (x.2.2.1 : ℤ) * Fz v (x.1 : ℤ)) := by
  rw [cauchyMulInt_eq_sum_Sols (f := fun a => xDivTerm u a - xDivTerm v a)
      (g := fun a => xDivTerm u a - xDivTerm v a) N
      (fun i hi => by
        show xCoeffFull u i - xCoeffFull v i
            = ∑ a ∈ i.divisors, (xDivTerm u a - xDivTerm v a)
        rw [xCoeffFull_of_pos u hi, xCoeffFull_of_pos v hi, xCoeff, xCoeff,
          ← Finset.sum_sub_distrib])
      (fun i hi => by
        show xCoeffFull u i - xCoeffFull v i
            = ∑ a ∈ i.divisors, (xDivTerm u a - xDivTerm v a)
        rw [xCoeffFull_of_pos u hi, xCoeffFull_of_pos v hi, xCoeff, xCoeff,
          ← Finset.sum_sub_distrib])]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [xDivTerm_eq_mul_Fz]
  have hu := Fz_mul_Fz hu0 (x.1 : ℤ) (x.2.2.1 : ℤ)
  have hv := Fz_mul_Fz hv0 (x.1 : ℤ) (x.2.2.1 : ℤ)
  linear_combination ((x.1 : K) * (x.2.2.1 : K)) * hu + ((x.1 : K) * (x.2.2.1 : K)) * hv

end CrossReadings
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz Fz_natCast Fz_mul_Fz xDivTerm_eq_mul_Fz a₆Coeff_of_pos tent xfun_mul_Fz_eq_tent cauchyMulInt_a4x_eq_neg_sum_Sols tent_eq_sq_add_sum_Ico add_le_of_mem_Sols cauchyMul xCoeffFull xCoeffFull_succ a₄Coeff a₄Coeff_succ a₆Coeff xfun yfun xfun_inv pointX pointY term b b_mul_twelve a₄ a₆ curve xDivTerm xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section GroupA

theorem groupA_cross_Fread (hu0 : u ≠ 0) (hv0 : v ≠ 0) (M : ℕ) :
    (∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) *
        ((u ^ x.1 - v ^ x.1) * (u ^ x.2.2.1 - v ^ x.2.2.1)
            * (u * v * (∑ i ∈ Finset.range x.1, (u * v) ^ i)
                * (∑ i ∈ Finset.range x.2.2.1, (u * v) ^ i)
                * ((u * v) ^ x.1)⁻¹ * ((u * v) ^ x.2.2.1)⁻¹)
          + (u ^ x.1 - (v ^ x.1)⁻¹) * (u ^ x.2.2.1 - (v ^ x.2.2.1)⁻¹)
              * (u * v⁻¹ * (∑ i ∈ Finset.range x.1, (u * v⁻¹) ^ i)
                  * (∑ i ∈ Finset.range x.2.2.1, (u * v⁻¹) ^ i)
                  * ((u * v⁻¹) ^ x.1)⁻¹ * ((u * v⁻¹) ^ x.2.2.1)⁻¹)))
      = ∑ x ∈ Sols M, ∑ i ∈ Finset.range x.1, ∑ i' ∈ Finset.range x.2.2.1,
          (x.1 : K) * (x.2.2.1 : K) *
            (Fz u ((i : ℤ) + i' + 1) * Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i')
              - Fz u ((i : ℤ) + i' + 1 - x.2.2.1) * Fz v ((i : ℤ) + i' + 1 - x.1)
              + 2 * (Fz u ((i : ℤ) + i' + 1) - Fz u ((i : ℤ) + i' + 1 - x.2.2.1))
              + 2 * (Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i')
                  - Fz v ((i : ℤ) + i' + 1 - x.1))) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [crossPair_expansion hu0 hv0 x.1 x.2.2.1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i' _ => by rw [crossPair_term_expand]

end GroupA
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

section GroupB

theorem groupB_tent_Fread [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ) :
    ∑ d ∈ M.divisors, (d : K) *
        ((∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j))
          - ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j))
      = ∑ d ∈ M.divisors, (d : K) *
          ((∑ j ∈ Finset.Icc 1 d,
              ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2
                + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j),
                    ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ))
                + ((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
                    ((j - l : ℕ) : K) * Fz v (l : ℤ))
                + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j),
                    ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K)
                      * Fz v (l : ℤ) * Fz u (l' : ℤ)))
            - ∑ j ∈ Finset.range d,
                ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2
                  + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j),
                      ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ))
                  + ((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
                      ((j - l : ℕ) : K) * Fz v (l : ℤ))
                  + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j),
                      ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K)
                        * Fz v (l : ℤ) * Fz u (l' : ℤ))) := by
  refine Finset.sum_congr rfl fun d _ => ?_
  have h1 : (∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j))
      = ∑ j ∈ Finset.Icc 1 d,
          ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2
            + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j),
                ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ))
            + ((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
                ((j - l : ℕ) : K) * Fz v (l : ℤ))
            + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j),
                ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K)
                  * Fz v (l : ℤ) * Fz u (l' : ℤ)) :=
    Finset.sum_congr rfl fun j _ => tent_mul_tent_eq hu0 hu1 hv0 hv1 j (d + 1 - j)
  have h2 : (∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j))
      = ∑ j ∈ Finset.range d,
          ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2
            + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j),
                ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ))
            + ((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
                ((j - l : ℕ) : K) * Fz v (l : ℤ))
            + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j),
                ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K)
                  * Fz v (l : ℤ) * Fz u (l' : ℤ)) :=
    Finset.sum_congr rfl fun j _ => tent_mul_tent_eq hu0 hu1 hv0 hv1 j (d - 1 - j)
  rw [h1, h2]

end GroupB
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

section GroupC

theorem groupC_square_Fread [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) (M : ℕ) :
    ∑ d ∈ M.divisors, (d : K) *
        ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k)
          + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k)
          - 2 * (tent u d * tent v d))
      = ∑ d ∈ M.divisors, (d : K) *
          ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) *
              ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ)))
            + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) *
                ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ)))
            - 2 * ((d : K) ^ 2 * (d : K) ^ 2
                + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ))
                + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ))
                + ∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d,
                    ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) := by
  refine Finset.sum_congr rfl fun d _ => ?_
  have hU : (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k)
      = ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) *
          ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ)) :=
    Finset.sum_congr rfl fun k _ => by rw [tent_eq_sq_add_sum_Ico hu0 hu1 k]
  have hV : (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k)
      = ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) *
          ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ)) :=
    Finset.sum_congr rfl fun k _ => by rw [tent_eq_sq_add_sum_Ico hv0 hv1 k]
  have hD : tent u d * tent v d
      = (d : K) ^ 2 * (d : K) ^ 2
          + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ))
          + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ))
          + ∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d,
              ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ) := by
    rw [mul_comm (tent u d) (tent v d), tent_mul_tent_eq hu0 hu1 hv0 hv1 d d]
  rw [hU, hV, hD]

end GroupC
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum cauchyMul_eq_sum_range cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz Fz_natCast Fz_mul_Fz xDivTerm_eq_mul_Fz a₆Coeff_of_pos tent xfun_mul_Fz_eq_tent cauchyMulInt_a4x_eq_neg_sum_Sols tent_eq_sq_add_sum_Ico add_le_of_mem_Sols cauchyMul xCoeffFull xCoeffFull_succ a₄Coeff a₄Coeff_succ a₆Coeff xfun yfun xfun_inv pointX pointY term b b_mul_twelve a₄ a₆ curve xDivTerm xCoeff addDefectDiff ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section PerIndex

theorem Fz_add_two_mul_Fz (hu0 : u ≠ 0) (a b : ℤ) :
    (Fz u a + 2) * Fz u b = Fz u (a + b) + Fz u (a - b) - 2 * Fz u a := by
  linear_combination Fz_mul_Fz hu0 a b

theorem crossFactor_mul_Fz_left (hu0 : u ≠ 0) (d a : ℤ) :
    (Fz u d * Fz v d + 2 * Fz u d + 2 * Fz v d) * Fz u a
      = Fz v d * (Fz u (d + a) + Fz u (d - a) - 2 * Fz u d - 2 * Fz u a)
        + 2 * (Fz u (d + a) + Fz u (d - a) - 2 * Fz u d - 2 * Fz u a)
        + 2 * Fz v d * Fz u a := by
  linear_combination (Fz v d + 2) * Fz_mul_Fz hu0 d a

theorem crossFactor_mul_Fz_right (hv0 : v ≠ 0) (d a : ℤ) :
    (Fz u d * Fz v d + 2 * Fz u d + 2 * Fz v d) * Fz v a
      = Fz u d * (Fz v (d + a) + Fz v (d - a) - 2 * Fz v d - 2 * Fz v a)
        + 2 * (Fz v (d + a) + Fz v (d - a) - 2 * Fz v d - 2 * Fz v a)
        + 2 * Fz u d * Fz v a := by
  linear_combination (Fz u d + 2) * Fz_mul_Fz hv0 d a

theorem Fz_mul_Fz_mul_Fz_mul_Fz (hu0 : u ≠ 0) (hv0 : v ≠ 0) (a b c d : ℤ) :
    (Fz u a * Fz v b) * (Fz u c * Fz v d)
      = (Fz u (a + c) + Fz u (a - c) - 2 * Fz u a - 2 * Fz u c)
        * (Fz v (b + d) + Fz v (b - d) - 2 * Fz v b - 2 * Fz v d) := by
  linear_combination (Fz v b * Fz v d) * Fz_mul_Fz hu0 a c
    + (Fz u (a + c) + Fz u (a - c) - 2 * Fz u a - 2 * Fz u c) * Fz_mul_Fz hv0 b d

theorem crossFactor_mul_tent_eq [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (d : ℤ) (e : ℕ) :
    (Fz u d * Fz v d + 2 * Fz u d + 2 * Fz v d) * tent u e
      = Fz v d * ((e : K) ^ 2 * Fz u d
            + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K)
                * (Fz u (d + (l : ℤ)) + Fz u (d - (l : ℤ)) - 2 * Fz u d - 2 * Fz u (l : ℤ)))
        + 2 * ((e : K) ^ 2 * Fz u d
            + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K)
                * (Fz u (d + (l : ℤ)) + Fz u (d - (l : ℤ)) - 2 * Fz u d - 2 * Fz u (l : ℤ)))
        + 2 * Fz v d
            * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz u (l : ℤ)) := by
  have h1 := Fz_mul_tent_eq hu0 hu1 d e
  have h2 := tent_eq_sq_add_sum_Ico hu0 hu1 e
  linear_combination (Fz v d + 2) * h1 + 2 * Fz v d * h2

theorem psiTent_mul_Fz_eq (hv0 : v ≠ 0) (d : ℕ) (a : ℤ) :
    ((Fz v (d : ℤ) + 2) * tent u d) * Fz v a
      = (Fz v ((d : ℤ) + a) + Fz v ((d : ℤ) - a) - 2 * Fz v (d : ℤ)) * tent u d := by
  linear_combination tent u d * Fz_mul_Fz hv0 (d : ℤ) a

end PerIndex
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

section BlockLevel

theorem groupD_cross_tent_Fread [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (M : ℕ) :
    ∑ a ∈ Finset.Ico 1 M,
        (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
          * (∑ e ∈ (M - a).divisors, (e : K) * tent u e)
      = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ e ∈ (M - a).divisors,
          (d : K) * (e : K)
            * (Fz v (d : ℤ) * ((e : K) ^ 2 * Fz u (d : ℤ)
                  + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K)
                      * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ))
                          - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ)))
              + 2 * ((e : K) ^ 2 * Fz u (d : ℤ)
                  + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K)
                      * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ))
                          - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ)))
              + 2 * Fz v (d : ℤ)
                  * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz u (l : ℤ))) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [xCoeff_mul_add_xCoeff_mul_inv hu0 hv0 a, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  linear_combination ((d : K) * (e : K)) * crossFactor_mul_tent_eq (v := v) hu0 hu1 (d : ℤ) e

theorem groupD_cross_tent_Fread' [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ) :
    ∑ a ∈ Finset.Ico 1 M,
        (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
          * (∑ e ∈ (M - a).divisors, (e : K) * tent v e)
      = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ e ∈ (M - a).divisors,
          (d : K) * (e : K)
            * (Fz u (d : ℤ) * ((e : K) ^ 2 * Fz v (d : ℤ)
                  + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K)
                      * (Fz v ((d : ℤ) + (l : ℤ)) + Fz v ((d : ℤ) - (l : ℤ))
                          - 2 * Fz v (d : ℤ) - 2 * Fz v (l : ℤ)))
              + 2 * ((e : K) ^ 2 * Fz v (d : ℤ)
                  + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K)
                      * (Fz v ((d : ℤ) + (l : ℤ)) + Fz v ((d : ℤ) - (l : ℤ))
                          - 2 * Fz v (d : ℤ) - 2 * Fz v (l : ℤ)))
              + 2 * Fz u (d : ℤ)
                  * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz v (l : ℤ))) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [xCoeff_mul_add_xCoeff_mul_inv hu0 hv0 a, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h1 := Fz_mul_tent_eq hv0 hv1 (d : ℤ) e
  have h2 := tent_eq_sq_add_sum_Ico hv0 hv1 e
  linear_combination ((d : K) * (e : K) * (Fz u (d : ℤ) + 2)) * h1
    + ((d : K) * (e : K) * 2 * Fz u (d : ℤ)) * h2

theorem groupD_psi_xCoeff_Fread (hv0 : v ≠ 0) (M : ℕ) :
    ∑ a ∈ Finset.Ico 1 M,
        (∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d) * xCoeff v (M - a)
      = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ d' ∈ (M - a).divisors,
          (d : K) * (d' : K)
            * ((Fz v ((d : ℤ) + (d' : ℤ)) + Fz v ((d : ℤ) - (d' : ℤ)) - 2 * Fz v (d : ℤ))
                * tent u d) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [xCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [xDivTerm_eq_mul_Fz]
  linear_combination ((d : K) * (d' : K)) * psiTent_mul_Fz_eq (u := u) hv0 d (d' : ℤ)

end BlockLevel
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_ks17_C2_exports.TateCurve"

theorem solution :

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      cauchyMulInt (xCoeffFull u) (xCoeffFull v) M = ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * Fz u (x.1 : ℤ) * Fz v (x.2.2.1 : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u : K) (M : ℕ),
      cauchyMulInt a₄Coeff (xCoeffFull u) M = -(∑ x ∈ Sols M, ((5 * x.1 ^ 3 : ℕ) : K) * ((x.2.2.1 : K) * Fz u (x.2.2.1 : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (v : K)
    (M : ℕ),
      ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1 = (∑ x ∈ Sols M, (x.1 : K) ^ 3 * (x.2.2.1 : K) * Fz v (x.2.2.1 : ℤ)) + ∑ x ∈ Sols M, ∑ j ∈ Finset.Ico 1 x.1, (x.1 : K) * ((x.1 - j : ℕ) : K) * (x.2.2.1 : K) * Fz u (j : ℤ) * Fz v (x.2.2.1 : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {v : K} [CharZero K] (u : K) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ),
      ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1) = (∑ x ∈ Sols M, (x.2.2.1 : K) ^ 3 * (x.1 : K) * Fz u (x.1 : ℤ)) + ∑ x ∈ Sols M, ∑ j ∈ Finset.Ico 1 x.2.2.1, (x.2.2.1 : K) * ((x.2.2.1 - j : ℕ) : K) * (x.1 : K) * Fz u (x.1 : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (v : K) (M : ℕ),
      cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i), (d : K) * (x.1 : K) * (x.2.2.1 : K) * (Fz u ((d : ℤ) + (x.1 : ℤ)) + Fz u ((d : ℤ) - (x.1 : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (x.1 : ℤ)) * Fz v (x.2.2.1 : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {v : K} (u : K) (hv0 : v ≠ 0) (M : ℕ),
      cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i), (d : K) * (x.1 : K) * (x.2.2.1 : K) * Fz u (d : ℤ) * (Fz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + Fz v ((x.1 : ℤ) - (x.2.2.1 : ℤ)) - 2 * Fz v (x.1 : ℤ) - 2 * Fz v (x.2.2.1 : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (d a : ℤ),
      (Fz u d * Fz v d + 2 * Fz u d + 2 * Fz v d) * Fz u a = Fz v d * (Fz u (d + a) + Fz u (d - a) - 2 * Fz u d - 2 * Fz u a) + 2 * (Fz u (d + a) + Fz u (d - a) - 2 * Fz u d - 2 * Fz u a) + 2 * Fz v d * Fz u a) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hv0 : v ≠ 0) (d a : ℤ),
      (Fz u d * Fz v d + 2 * Fz u d + 2 * Fz v d) * Fz v a = Fz u d * (Fz v (d + a) + Fz v (d - a) - 2 * Fz v d - 2 * Fz v a) + 2 * (Fz v (d + a) + Fz v (d - a) - 2 * Fz v d - 2 * Fz v a) + 2 * Fz u d * Fz v a) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (a b c d : ℤ),
      (Fz u a * Fz v b) * (Fz u c * Fz v d) = (Fz u (a + c) + Fz u (a - c) - 2 * Fz u a - 2 * Fz u c) * (Fz v (b + d) + Fz v (b - d) - 2 * Fz v b - 2 * Fz v d)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [CharZero K] {M : ℕ} (hM : 0 < M),
      -2 * ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, (j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2) - ∑ j ∈ Finset.range d, (j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2) + ∑ d ∈ M.divisors, (d : K) * (2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2 + 2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2 - 2 * ((d : K) ^ 2 * (d : K) ^ 2)) - 4 * a₆Coeff M = 0) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (M : ℕ),
      (∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * ((u ^ x.1 - v ^ x.1) * (u ^ x.2.2.1 - v ^ x.2.2.1) * (u * v * (∑ i ∈ Finset.range x.1, (u * v) ^ i) * (∑ i ∈ Finset.range x.2.2.1, (u * v) ^ i) * ((u * v) ^ x.1)⁻¹ * ((u * v) ^ x.2.2.1)⁻¹) + (u ^ x.1 - (v ^ x.1)⁻¹) * (u ^ x.2.2.1 - (v ^ x.2.2.1)⁻¹) * (u * v⁻¹ * (∑ i ∈ Finset.range x.1, (u * v⁻¹) ^ i) * (∑ i ∈ Finset.range x.2.2.1, (u * v⁻¹) ^ i) * ((u * v⁻¹) ^ x.1)⁻¹ * ((u * v⁻¹) ^ x.2.2.1)⁻¹))) = ∑ x ∈ Sols M, ∑ i ∈ Finset.range x.1, ∑ i' ∈ Finset.range x.2.2.1, (x.1 : K) * (x.2.2.1 : K) * (Fz u ((i : ℤ) + i' + 1) * Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i') - Fz u ((i : ℤ) + i' + 1 - x.2.2.1) * Fz v ((i : ℤ) + i' + 1 - x.1) + 2 * (Fz u ((i : ℤ) + i' + 1) - Fz u ((i : ℤ) + i' + 1 - x.2.2.1)) + 2 * (Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i') - Fz v ((i : ℤ) + i' + 1 - x.1)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ),
      ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j)) - ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j)) = ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2 + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j), ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ)) + ((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j), ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) - ∑ j ∈ Finset.range d, ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2 + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j), ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ)) + ((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j), ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) (M : ℕ),
      ∑ d ∈ M.divisors, (d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k) + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k) - 2 * (tent u d * tent v d)) = ∑ d ∈ M.divisors, (d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ))) + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ))) - 2 * ((d : K) ^ 2 * (d : K) ^ 2 + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ)) + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * (∑ e ∈ (M - a).divisors, (e : K) * tent u e) = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ e ∈ (M - a).divisors, (d : K) * (e : K) * (Fz v (d : ℤ) * ((e : K) ^ 2 * Fz u (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ))) + 2 * ((e : K) ^ 2 * Fz u (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ))) + 2 * Fz v (d : ℤ) * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz u (l : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * (∑ e ∈ (M - a).divisors, (e : K) * tent v e) = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ e ∈ (M - a).divisors, (d : K) * (e : K) * (Fz u (d : ℤ) * ((e : K) ^ 2 * Fz v (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz v ((d : ℤ) + (l : ℤ)) + Fz v ((d : ℤ) - (l : ℤ)) - 2 * Fz v (d : ℤ) - 2 * Fz v (l : ℤ))) + 2 * ((e : K) ^ 2 * Fz v (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz v ((d : ℤ) + (l : ℤ)) + Fz v ((d : ℤ) - (l : ℤ)) - 2 * Fz v (d : ℤ) - 2 * Fz v (l : ℤ))) + 2 * Fz u (d : ℤ) * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz v (l : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hv0 : v ≠ 0) (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d) * xCoeff v (M - a) = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ d' ∈ (M - a).divisors, (d : K) * (d' : K) * ((Fz v ((d : ℤ) + (d' : ℤ)) + Fz v ((d : ℤ) - (d' : ℤ)) - 2 * Fz v (d : ℤ)) * tent u d)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M),
      addDefectSumCoeff u v M = (∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * ((u ^ x.1 - v ^ x.1) * (u ^ x.2.2.1 - v ^ x.2.2.1) * (u * v * (∑ i ∈ Finset.range x.1, (u * v) ^ i) * (∑ i ∈ Finset.range x.2.2.1, (u * v) ^ i) * ((u * v) ^ x.1)⁻¹ * ((u * v) ^ x.2.2.1)⁻¹) + (u ^ x.1 - (v ^ x.1)⁻¹) * (u ^ x.2.2.1 - (v ^ x.2.2.1)⁻¹) * (u * v⁻¹ * (∑ i ∈ Finset.range x.1, (u * v⁻¹) ^ i) * (∑ i ∈ Finset.range x.2.2.1, (u * v⁻¹) ^ i) * ((u * v⁻¹) ^ x.1)⁻¹ * ((u * v⁻¹) ^ x.2.2.1)⁻¹))) - 2 * ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j)) - ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j)) + (∑ d ∈ M.divisors, (d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k) + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k) - 2 * (tent u d * tent v d))) + (∑ a ∈ Finset.Ico 1 M, ((xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * (2 * ((∑ e ∈ (M - a).divisors, (e : K) * tent u e) + ∑ e ∈ (M - a).divisors, (e : K) * tent v e) + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)) - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d) * xCoeff v (M - a)) - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz u (d : ℤ) + 2) * tent v d) * xCoeff u (M - a)))) - 4 * ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1 - 4 * ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1) - 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M - 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M - cauchyMulInt (xCoeffFull u) (xCoeffFull v) M - 2 * cauchyMulInt a₄Coeff (xCoeffFull u) M - 2 * cauchyMulInt a₄Coeff (xCoeffFull v) M - 4 * a₆Coeff M) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} [IsUltrametricDist K] [CompleteSpace K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huvd : u * v⁻¹ ≠ 1) (M : ℕ),
      addDefectSumCoeff v u M = addDefectSumCoeff u v M) :=
  ⟨TateCurve.cauchyMulInt_x_x_eq_sum_Sols_Fz,
   TateCurve.cauchyMulInt_a₄_x_eq_sum_Sols_Fz,
   TateCurve.sum_Sols_tent_xDivTerm_eq_Fz,
   TateCurve.sum_Sols_xDivTerm_tent_eq_Fz,
   TateCurve.cauchyMulIntTriple_xxv_eq_sum_Fz,
   TateCurve.cauchyMulIntTriple_xvv_eq_sum_Fz,
   TateCurve.crossFactor_mul_Fz_left,
   TateCurve.crossFactor_mul_Fz_right,
   TateCurve.Fz_mul_Fz_mul_Fz_mul_Fz,
   TateCurve.constantBin_eq_zero,
   TateCurve.groupA_cross_Fread,
   TateCurve.groupB_tent_Fread,
   TateCurve.groupC_square_Fread,
   TateCurve.groupD_cross_tent_Fread,
   TateCurve.groupD_cross_tent_Fread',
   TateCurve.groupD_psi_xCoeff_Fread,
   TateCurve.addDefectSumCoeff_eq_absorbed,
   TateCurve.addDefectSumCoeff_swap⟩

end S_TateCurve_ks17_C2_exports
end P2MW
export P2MW.S_TateCurve_ks17_C2_exports (solution)
