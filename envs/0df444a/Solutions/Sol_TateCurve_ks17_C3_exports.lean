-- Prove2me | solution 1 for TateCurve.ks17_C3_exports
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/18956e9a-8da3-58bc-9c33-eeccd71de763

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_DefectLines
import Definitions.Def_NumberTheory_DivisorConvolution
import Definitions.Def_TateCurve_KeystoneVocab

import Theorems.Thm_TateCurve_ks17_B_exports
import Theorems.Thm_TateCurve_ks17_C2_exports
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

namespace P2MW.S_TateCurve_ks17_C3_exports

open scoped NNReal
p2m_open "TateCurve P2MW.S_TateCurve_ks17_C3_exports.TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset"

universe u_1 u_2

namespace TateCurve
p2m_export "TateCurve" "cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz xDivTerm_eq_mul_Fz tent Fz_natAbs add_le_of_mem_Sols sum_mul_Fz_eq_sum_lines_nat sum_mul_Fz_eq_sum_lines_int cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun b a₄ curve xDivTerm xCoeff addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex ks17_B_exports ks17_C2_exports"
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

namespace TateCurve
p2m_export "TateCurve" "cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz xDivTerm_eq_mul_Fz tent Fz_natAbs add_le_of_mem_Sols sum_mul_Fz_eq_sum_lines_nat sum_mul_Fz_eq_sum_lines_int cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun b a₄ curve xDivTerm xCoeff addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex ks17_B_exports ks17_C2_exports"
p2m_open "TateCurve"

theorem cauchyMulInt_x_x_eq_sum_Sols_Fz : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      cauchyMulInt (xCoeffFull u) (xCoeffFull v) M = ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * Fz u (x.1 : ℤ) * Fz v (x.2.2.1 : ℤ) :=
  TateCurve.ks17_C2_exports.{u_1}.1

theorem cauchyMulInt_a₄_x_eq_sum_Sols_Fz : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u : K) (M : ℕ),
      cauchyMulInt a₄Coeff (xCoeffFull u) M = -(∑ x ∈ Sols M, ((5 * x.1 ^ 3 : ℕ) : K) * ((x.2.2.1 : K) * Fz u (x.2.2.1 : ℤ))) :=
  TateCurve.ks17_C2_exports.{u_1}.2.1

theorem sum_Sols_tent_xDivTerm_eq_Fz : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (v : K)
    (M : ℕ),
      ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1 = (∑ x ∈ Sols M, (x.1 : K) ^ 3 * (x.2.2.1 : K) * Fz v (x.2.2.1 : ℤ)) + ∑ x ∈ Sols M, ∑ j ∈ Finset.Ico 1 x.1, (x.1 : K) * ((x.1 - j : ℕ) : K) * (x.2.2.1 : K) * Fz u (j : ℤ) * Fz v (x.2.2.1 : ℤ) :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.1

theorem sum_Sols_xDivTerm_tent_eq_Fz : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {v : K} [CharZero K] (u : K) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ),
      ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1) = (∑ x ∈ Sols M, (x.2.2.1 : K) ^ 3 * (x.1 : K) * Fz u (x.1 : ℤ)) + ∑ x ∈ Sols M, ∑ j ∈ Finset.Ico 1 x.2.2.1, (x.2.2.1 : K) * ((x.2.2.1 - j : ℕ) : K) * (x.1 : K) * Fz u (x.1 : ℤ) * Fz v (j : ℤ) :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.1

theorem cauchyMulIntTriple_xxv_eq_sum_Fz : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (v : K) (M : ℕ),
      cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i), (d : K) * (x.1 : K) * (x.2.2.1 : K) * (Fz u ((d : ℤ) + (x.1 : ℤ)) + Fz u ((d : ℤ) - (x.1 : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (x.1 : ℤ)) * Fz v (x.2.2.1 : ℤ) :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.1

theorem cauchyMulIntTriple_xvv_eq_sum_Fz : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {v : K} (u : K) (hv0 : v ≠ 0) (M : ℕ),
      cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i), (d : K) * (x.1 : K) * (x.2.2.1 : K) * Fz u (d : ℤ) * (Fz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + Fz v ((x.1 : ℤ) - (x.2.2.1 : ℤ)) - 2 * Fz v (x.1 : ℤ) - 2 * Fz v (x.2.2.1 : ℤ)) :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.1

theorem crossFactor_mul_Fz_left : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (d a : ℤ),
      (Fz u d * Fz v d + 2 * Fz u d + 2 * Fz v d) * Fz u a = Fz v d * (Fz u (d + a) + Fz u (d - a) - 2 * Fz u d - 2 * Fz u a) + 2 * (Fz u (d + a) + Fz u (d - a) - 2 * Fz u d - 2 * Fz u a) + 2 * Fz v d * Fz u a :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.2.1

theorem crossFactor_mul_Fz_right : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hv0 : v ≠ 0) (d a : ℤ),
      (Fz u d * Fz v d + 2 * Fz u d + 2 * Fz v d) * Fz v a = Fz u d * (Fz v (d + a) + Fz v (d - a) - 2 * Fz v d - 2 * Fz v a) + 2 * (Fz v (d + a) + Fz v (d - a) - 2 * Fz v d - 2 * Fz v a) + 2 * Fz u d * Fz v a :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.2.2.1

theorem Fz_mul_Fz_mul_Fz_mul_Fz : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (a b c d : ℤ),
      (Fz u a * Fz v b) * (Fz u c * Fz v d) = (Fz u (a + c) + Fz u (a - c) - 2 * Fz u a - 2 * Fz u c) * (Fz v (b + d) + Fz v (b - d) - 2 * Fz v b - 2 * Fz v d) :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.2.2.2.1

theorem constantBin_eq_zero : ∀ {K : Type u_1} [NontriviallyNormedField K] [CharZero K] {M : ℕ} (hM : 0 < M),
      -2 * ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, (j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2) - ∑ j ∈ Finset.range d, (j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2) + ∑ d ∈ M.divisors, (d : K) * (2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2 + 2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2 - 2 * ((d : K) ^ 2 * (d : K) ^ 2)) - 4 * a₆Coeff M = 0 :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.2.2.2.2.1

theorem groupA_cross_Fread : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (M : ℕ),
      (∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * ((u ^ x.1 - v ^ x.1) * (u ^ x.2.2.1 - v ^ x.2.2.1) * (u * v * (∑ i ∈ Finset.range x.1, (u * v) ^ i) * (∑ i ∈ Finset.range x.2.2.1, (u * v) ^ i) * ((u * v) ^ x.1)⁻¹ * ((u * v) ^ x.2.2.1)⁻¹) + (u ^ x.1 - (v ^ x.1)⁻¹) * (u ^ x.2.2.1 - (v ^ x.2.2.1)⁻¹) * (u * v⁻¹ * (∑ i ∈ Finset.range x.1, (u * v⁻¹) ^ i) * (∑ i ∈ Finset.range x.2.2.1, (u * v⁻¹) ^ i) * ((u * v⁻¹) ^ x.1)⁻¹ * ((u * v⁻¹) ^ x.2.2.1)⁻¹))) = ∑ x ∈ Sols M, ∑ i ∈ Finset.range x.1, ∑ i' ∈ Finset.range x.2.2.1, (x.1 : K) * (x.2.2.1 : K) * (Fz u ((i : ℤ) + i' + 1) * Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i') - Fz u ((i : ℤ) + i' + 1 - x.2.2.1) * Fz v ((i : ℤ) + i' + 1 - x.1) + 2 * (Fz u ((i : ℤ) + i' + 1) - Fz u ((i : ℤ) + i' + 1 - x.2.2.1)) + 2 * (Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i') - Fz v ((i : ℤ) + i' + 1 - x.1))) :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.1

theorem groupB_tent_Fread : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ),
      ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j)) - ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j)) = ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2 + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j), ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ)) + ((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j), ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) - ∑ j ∈ Finset.range d, ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2 + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j), ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ)) + ((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j), ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.1

theorem groupC_square_Fread : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) (M : ℕ),
      ∑ d ∈ M.divisors, (d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k) + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k) - 2 * (tent u d * tent v d)) = ∑ d ∈ M.divisors, (d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ))) + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ))) - 2 * ((d : K) ^ 2 * (d : K) ^ 2 + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ)) + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem groupD_cross_tent_Fread : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * (∑ e ∈ (M - a).divisors, (e : K) * tent u e) = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ e ∈ (M - a).divisors, (d : K) * (e : K) * (Fz v (d : ℤ) * ((e : K) ^ 2 * Fz u (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ))) + 2 * ((e : K) ^ 2 * Fz u (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ))) + 2 * Fz v (d : ℤ) * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz u (l : ℤ))) :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem groupD_cross_tent_Fread' : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * (∑ e ∈ (M - a).divisors, (e : K) * tent v e) = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ e ∈ (M - a).divisors, (d : K) * (e : K) * (Fz u (d : ℤ) * ((e : K) ^ 2 * Fz v (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz v ((d : ℤ) + (l : ℤ)) + Fz v ((d : ℤ) - (l : ℤ)) - 2 * Fz v (d : ℤ) - 2 * Fz v (l : ℤ))) + 2 * ((e : K) ^ 2 * Fz v (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz v ((d : ℤ) + (l : ℤ)) + Fz v ((d : ℤ) - (l : ℤ)) - 2 * Fz v (d : ℤ) - 2 * Fz v (l : ℤ))) + 2 * Fz u (d : ℤ) * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz v (l : ℤ))) :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem groupD_psi_xCoeff_Fread : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hv0 : v ≠ 0) (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d) * xCoeff v (M - a) = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ d' ∈ (M - a).divisors, (d : K) * (d' : K) * ((Fz v ((d : ℤ) + (d' : ℤ)) + Fz v ((d : ℤ) - (d' : ℤ)) - 2 * Fz v (d : ℤ)) * tent u d) :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem addDefectSumCoeff_eq_absorbed : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M),
      addDefectSumCoeff u v M = (∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * ((u ^ x.1 - v ^ x.1) * (u ^ x.2.2.1 - v ^ x.2.2.1) * (u * v * (∑ i ∈ Finset.range x.1, (u * v) ^ i) * (∑ i ∈ Finset.range x.2.2.1, (u * v) ^ i) * ((u * v) ^ x.1)⁻¹ * ((u * v) ^ x.2.2.1)⁻¹) + (u ^ x.1 - (v ^ x.1)⁻¹) * (u ^ x.2.2.1 - (v ^ x.2.2.1)⁻¹) * (u * v⁻¹ * (∑ i ∈ Finset.range x.1, (u * v⁻¹) ^ i) * (∑ i ∈ Finset.range x.2.2.1, (u * v⁻¹) ^ i) * ((u * v⁻¹) ^ x.1)⁻¹ * ((u * v⁻¹) ^ x.2.2.1)⁻¹))) - 2 * ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j)) - ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j)) + (∑ d ∈ M.divisors, (d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k) + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k) - 2 * (tent u d * tent v d))) + (∑ a ∈ Finset.Ico 1 M, ((xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * (2 * ((∑ e ∈ (M - a).divisors, (e : K) * tent u e) + ∑ e ∈ (M - a).divisors, (e : K) * tent v e) + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)) - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d) * xCoeff v (M - a)) - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz u (d : ℤ) + 2) * tent v d) * xCoeff u (M - a)))) - 4 * ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1 - 4 * ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1) - 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M - 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M - cauchyMulInt (xCoeffFull u) (xCoeffFull v) M - 2 * cauchyMulInt a₄Coeff (xCoeffFull u) M - 2 * cauchyMulInt a₄Coeff (xCoeffFull v) M - 4 * a₆Coeff M :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem addDefectSumCoeff_swap : ∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} [IsUltrametricDist K] [CompleteSpace K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huvd : u * v⁻¹ ≠ 1) (M : ℕ),
      addDefectSumCoeff v u M = addDefectSumCoeff u v M :=
  TateCurve.ks17_C2_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz xDivTerm_eq_mul_Fz tent Fz_natAbs add_le_of_mem_Sols sum_mul_Fz_eq_sum_lines_nat sum_mul_Fz_eq_sum_lines_int cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun b a₄ curve xDivTerm xCoeff addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex ks17_B_exports ks17_C2_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section Collapse2

theorem sum_mul_Fz_Fz_eq_sum_lines_nat {α : Type*} (S : Finset α) (w : α → K) (g h : α → ℕ)
    {N : ℕ} (hg : ∀ x ∈ S, g x ≤ N) (hh : ∀ x ∈ S, h x ≤ N) :
    ∑ x ∈ S, w x * Fz u (g x : ℤ) * Fz v (h x : ℤ)
      = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => g x = k ∧ h x = j), w x)
            * Fz u (k : ℤ) * Fz v (j : ℤ) := by
  calc ∑ x ∈ S, w x * Fz u (g x : ℤ) * Fz v (h x : ℤ)
      = ∑ x ∈ S, (w x * Fz v (h x : ℤ)) * Fz u (g x : ℤ) :=
        Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ k ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => g x = k), w x * Fz v (h x : ℤ)) * Fz u (k : ℤ) :=
        sum_mul_Fz_eq_sum_lines_nat S _ g hg
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => g x = k ∧ h x = j), w x)
            * Fz u (k : ℤ) * Fz v (j : ℤ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sum_mul_Fz_eq_sum_lines_nat (S.filter fun x => g x = k) w h
          (fun x hx => hh x (Finset.mem_filter.mp hx).1), Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.filter_filter]
        ring

theorem sum_mul_Fz_Fz_eq_sum_lines_int {α : Type*} (S : Finset α) (w : α → K) (g h : α → ℤ)
    {N : ℕ} (hg : ∀ x ∈ S, (g x).natAbs ≤ N) (hh : ∀ x ∈ S, (h x).natAbs ≤ N) :
    ∑ x ∈ S, w x * Fz u (g x) * Fz v (h x)
      = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => (g x).natAbs = k ∧ (h x).natAbs = j), w x)
            * Fz u (k : ℤ) * Fz v (j : ℤ) := by
  calc ∑ x ∈ S, w x * Fz u (g x) * Fz v (h x)
      = ∑ x ∈ S, w x * Fz u ((g x).natAbs : ℤ) * Fz v ((h x).natAbs : ℤ) :=
        Finset.sum_congr rfl fun x _ => by rw [Fz_natAbs, Fz_natAbs]
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => (g x).natAbs = k ∧ (h x).natAbs = j), w x)
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
        sum_mul_Fz_Fz_eq_sum_lines_nat S w (fun x => (g x).natAbs) (fun x => (h x).natAbs)
          hg hh

end Collapse2

section FlatGroups

theorem groupH_eq_sum_lines (u v : K) (M : ℕ) :
    cauchyMulInt (xCoeffFull u) (xCoeffFull v) M
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ x ∈ (Sols M).filter (fun x => x.1 = k ∧ x.2.2.1 = j),
              (x.1 : K) * (x.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ) := by
  rw [cauchyMulInt_x_x_eq_sum_Sols_Fz]
  exact sum_mul_Fz_Fz_eq_sum_lines_nat (Sols M)
    (fun x => (x.1 : K) * (x.2.2.1 : K)) (fun x => x.1) (fun x => x.2.2.1)
    (fun x hx => le_trans (Nat.le_add_right _ _) (add_le_of_mem_Sols hx))
    (fun x hx => le_trans (Nat.le_add_left _ _) (add_le_of_mem_Sols hx))

theorem groupI_eq_sum_lines (u : K) (M : ℕ) :
    cauchyMulInt a₄Coeff (xCoeffFull u) M
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = k),
              -((5 * x.1 ^ 3 : ℕ) : K) * (x.2.2.1 : K)) * Fz u (k : ℤ) := by
  rw [cauchyMulInt_a₄_x_eq_sum_Sols_Fz]
  have h1 : -(∑ x ∈ Sols M, ((5 * x.1 ^ 3 : ℕ) : K) * ((x.2.2.1 : K) * Fz u (x.2.2.1 : ℤ)))
      = ∑ x ∈ Sols M, (-((5 * x.1 ^ 3 : ℕ) : K) * (x.2.2.1 : K)) * Fz u (x.2.2.1 : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h1]
  exact sum_mul_Fz_eq_sum_lines_nat (Sols M)
    (fun x => -((5 * x.1 ^ 3 : ℕ) : K) * (x.2.2.1 : K)) (fun x => x.2.2.1)
    (fun x hx => le_trans (Nat.le_add_left _ _) (add_le_of_mem_Sols hx))

end FlatGroups

section TentRows

theorem groupE1_eq_sum_lines [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (v : K) (M : ℕ) :
    ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1
      = (∑ j ∈ Finset.Icc 1 M,
            (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = j), (x.1 : K) ^ 3 * (x.2.2.1 : K))
              * Fz v (j : ℤ))
        + ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ p ∈ ((Sols M).sigma fun x => Finset.Ico 1 x.1).filter
                (fun p => p.2 = k ∧ p.1.2.2.1 = j),
              (p.1.1 : K) * ((p.1.1 - p.2 : ℕ) : K) * (p.1.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ) := by
  rw [sum_Sols_tent_xDivTerm_eq_Fz hu0 hu1 v M]
  congr 1
  ·
    exact sum_mul_Fz_eq_sum_lines_nat (Sols M)
      (fun x => (x.1 : K) ^ 3 * (x.2.2.1 : K)) (fun x => x.2.2.1)
      (fun x hx => le_trans (Nat.le_add_left _ _) (add_le_of_mem_Sols hx))
  ·
    have hflat : ∑ x ∈ Sols M, ∑ j ∈ Finset.Ico 1 x.1,
          (x.1 : K) * ((x.1 - j : ℕ) : K) * (x.2.2.1 : K)
            * Fz u (j : ℤ) * Fz v (x.2.2.1 : ℤ)
        = ∑ p ∈ (Sols M).sigma (fun x => Finset.Ico 1 x.1),
            (p.1.1 : K) * ((p.1.1 - p.2 : ℕ) : K) * (p.1.2.2.1 : K)
              * Fz u (p.2 : ℤ) * Fz v (p.1.2.2.1 : ℤ) := by
      rw [Finset.sum_sigma']
    rw [hflat]
    exact sum_mul_Fz_Fz_eq_sum_lines_nat ((Sols M).sigma fun x => Finset.Ico 1 x.1)
      (fun p => (p.1.1 : K) * ((p.1.1 - p.2 : ℕ) : K) * (p.1.2.2.1 : K))
      (fun p => p.2) (fun p => p.1.2.2.1)
      (fun p hp => by
        show p.2 ≤ M
        have h1 := Finset.mem_sigma.mp hp
        have h2 := add_le_of_mem_Sols h1.1
        have h3 := (Finset.mem_Ico.mp h1.2).2
        omega)
      (fun p hp => by
        show p.1.2.2.1 ≤ M
        have h1 := Finset.mem_sigma.mp hp
        have h2 := add_le_of_mem_Sols h1.1
        omega)

theorem groupE2_eq_sum_lines [CharZero K] (u : K) (hv0 : v ≠ 0) (hv1 : v ≠ 1) (M : ℕ) :
    ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1)
      = (∑ k ∈ Finset.Icc 1 M,
            (∑ x ∈ (Sols M).filter (fun x => x.1 = k), (x.2.2.1 : K) ^ 3 * (x.1 : K))
              * Fz u (k : ℤ))
        + ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ p ∈ ((Sols M).sigma fun x => Finset.Ico 1 x.2.2.1).filter
                (fun p => p.1.1 = k ∧ p.2 = j),
              (p.1.2.2.1 : K) * ((p.1.2.2.1 - p.2 : ℕ) : K) * (p.1.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ) := by
  rw [sum_Sols_xDivTerm_tent_eq_Fz u hv0 hv1 M]
  congr 1
  ·
    exact sum_mul_Fz_eq_sum_lines_nat (Sols M)
      (fun x => (x.2.2.1 : K) ^ 3 * (x.1 : K)) (fun x => x.1)
      (fun x hx => le_trans (Nat.le_add_right _ _) (add_le_of_mem_Sols hx))
  ·
    have hflat : ∑ x ∈ Sols M, ∑ j ∈ Finset.Ico 1 x.2.2.1,
          (x.2.2.1 : K) * ((x.2.2.1 - j : ℕ) : K) * (x.1 : K)
            * Fz u (x.1 : ℤ) * Fz v (j : ℤ)
        = ∑ p ∈ (Sols M).sigma (fun x => Finset.Ico 1 x.2.2.1),
            (p.1.2.2.1 : K) * ((p.1.2.2.1 - p.2 : ℕ) : K) * (p.1.1 : K)
              * Fz u (p.1.1 : ℤ) * Fz v (p.2 : ℤ) := by
      rw [Finset.sum_sigma']
    rw [hflat]
    exact sum_mul_Fz_Fz_eq_sum_lines_nat ((Sols M).sigma fun x => Finset.Ico 1 x.2.2.1)
      (fun p => (p.1.2.2.1 : K) * ((p.1.2.2.1 - p.2 : ℕ) : K) * (p.1.1 : K))
      (fun p => p.1.1) (fun p => p.2)
      (fun p hp => by
        show p.1.1 ≤ M
        have h1 := Finset.mem_sigma.mp hp
        have h2 := add_le_of_mem_Sols h1.1
        omega)
      (fun p hp => by
        show p.2 ≤ M
        have h1 := Finset.mem_sigma.mp hp
        have h2 := add_le_of_mem_Sols h1.1
        have h3 := (Finset.mem_Ico.mp h1.2).2
        omega)

end TentRows

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz xDivTerm_eq_mul_Fz tent Fz_natAbs add_le_of_mem_Sols sum_mul_Fz_eq_sum_lines_nat sum_mul_Fz_eq_sum_lines_int cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun b a₄ curve xDivTerm xCoeff addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex ks17_B_exports ks17_C2_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section MixedCollapse

theorem sum_mul_Fz_Fz_eq_sum_lines_int_nat {α : Type*} (S : Finset α) (w : α → K) (g : α → ℤ)
    (h : α → ℕ) {N : ℕ} (hg : ∀ x ∈ S, (g x).natAbs ≤ N) (hh : ∀ x ∈ S, h x ≤ N) :
    ∑ x ∈ S, w x * Fz u (g x) * Fz v (h x : ℤ)
      = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => (g x).natAbs = k ∧ h x = j), w x)
            * Fz u (k : ℤ) * Fz v (j : ℤ) := by
  calc ∑ x ∈ S, w x * Fz u (g x) * Fz v (h x : ℤ)
      = ∑ x ∈ S, w x * Fz u ((g x).natAbs : ℤ) * Fz v (h x : ℤ) :=
        Finset.sum_congr rfl fun x _ => by rw [Fz_natAbs]
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => (g x).natAbs = k ∧ h x = j), w x)
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
        sum_mul_Fz_Fz_eq_sum_lines_nat S w (fun x => (g x).natAbs) h hg hh

theorem sum_mul_Fz_Fz_eq_sum_lines_nat_int {α : Type*} (S : Finset α) (w : α → K) (g : α → ℕ)
    (h : α → ℤ) {N : ℕ} (hg : ∀ x ∈ S, g x ≤ N) (hh : ∀ x ∈ S, (h x).natAbs ≤ N) :
    ∑ x ∈ S, w x * Fz u (g x : ℤ) * Fz v (h x)
      = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => g x = k ∧ (h x).natAbs = j), w x)
            * Fz u (k : ℤ) * Fz v (j : ℤ) := by
  calc ∑ x ∈ S, w x * Fz u (g x : ℤ) * Fz v (h x)
      = ∑ x ∈ S, w x * Fz u (g x : ℤ) * Fz v ((h x).natAbs : ℤ) :=
        Finset.sum_congr rfl fun x _ => by rw [Fz_natAbs]
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => g x = k ∧ (h x).natAbs = j), w x)
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
        sum_mul_Fz_Fz_eq_sum_lines_nat S w g (fun x => (h x).natAbs) hg hh

end MixedCollapse

section TripleIndex

theorem sum_Ico_divisors_Sols_eq_sigma {β : Type*} [AddCommMonoid β] (M : ℕ)
    (f : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ → β) :
    ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i), f i d x
      = ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1),
          f q.1.1 q.1.2 q.2 :=
  calc ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i), f i d x
      = ∑ p ∈ (Finset.Ico 1 M).sigma fun i => i.divisors, ∑ x ∈ Sols (M - p.1), f p.1 p.2 x :=
        Finset.sum_sigma' (Finset.Ico 1 M) (fun i => i.divisors)
          (fun i d => ∑ x ∈ Sols (M - i), f i d x)
    _ = ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1),
          f q.1.1 q.1.2 q.2 :=
        Finset.sum_sigma' ((Finset.Ico 1 M).sigma fun i => i.divisors)
          (fun p => Sols (M - p.1)) (fun p x => f p.1 p.2 x)

private theorem bounds_of_mem_tripleIdx_C3Collapse2 {M : ℕ}
    {q : Σ _ : (Σ _ : ℕ, ℕ), ℕ × ℕ × ℕ × ℕ}
    (hq : q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)) :
    1 ≤ q.1.1 ∧ q.1.1 < M ∧ q.1.2 ≤ q.1.1 ∧ q.2.1 + q.2.2.2.1 ≤ M - q.1.1 := by
  have h1 := Finset.mem_sigma.mp hq
  have h2 := Finset.mem_sigma.mp h1.1
  have h3 := Finset.mem_Ico.mp h2.1
  have h4 : q.1.2 ∣ q.1.1 := (Nat.mem_divisors.mp h2.2).1
  have h5 := add_le_of_mem_Sols h1.2
  exact ⟨h3.1, h3.2, Nat.le_of_dvd (by omega) h4, h5⟩

end TripleIndex

section Triples

set_option maxHeartbeats 3200000 in

theorem groupF_eq_sum_lines (hu0 : u ≠ 0) (v : K) (M : ℕ) :
    cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.1.2 = k ∧ q.2.2.2.1 = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.2.1 = k ∧ q.2.2.2.1 = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ)) := by
  have hc0 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) * Fz v (q.2.2.2.1 : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + (q.2.1 : ℤ)) (fun q => q.2.2.2.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show q.2.2.2.1 ≤ M
        omega)
  have hc1 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ)) * Fz v (q.2.2.2.1 : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) - (q.2.1 : ℤ)) (fun q => q.2.2.2.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show q.2.2.2.1 ≤ M
        omega)
  have hc2 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u (q.1.2 : ℤ) * Fz v (q.2.2.2.1 : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k ∧ q.2.2.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.1.2) (fun q => q.2.2.2.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show q.1.2 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show q.2.2.2.1 ≤ M
        omega)
  have hc3 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.2.1 = k ∧ q.2.2.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.2.1) (fun q => q.2.2.2.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show q.2.1 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show q.2.2.2.1 ≤ M
        omega)
  have hsplit : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * (Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ))
                - 2 * Fz u (q.1.2 : ℤ) - 2 * Fz u (q.2.1 : ℤ))
            * Fz v (q.2.2.2.1 : ℤ))
      = (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) * Fz v (q.2.2.2.1 : ℤ))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ)) * Fz v (q.2.2.2.1 : ℤ))
        - 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u (q.1.2 : ℤ) * Fz v (q.2.2.2.1 : ℤ))
        - 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  calc cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M
      = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i),
          (d : K) * (x.1 : K) * (x.2.2.1 : K)
            * (Fz u ((d : ℤ) + (x.1 : ℤ)) + Fz u ((d : ℤ) - (x.1 : ℤ))
                - 2 * Fz u (d : ℤ) - 2 * Fz u (x.1 : ℤ))
            * Fz v (x.2.2.1 : ℤ) := cauchyMulIntTriple_xxv_eq_sum_Fz hu0 v M
    _ = ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
          fun p => Sols (M - p.1),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
              * (Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ))
                  - 2 * Fz u (q.1.2 : ℤ) - 2 * Fz u (q.2.1 : ℤ))
              * Fz v (q.2.2.2.1 : ℤ) :=
        sum_Ico_divisors_Sols_eq_sigma M
          (fun i d x => (d : K) * (x.1 : K) * (x.2.2.1 : K)
            * (Fz u ((d : ℤ) + (x.1 : ℤ)) + Fz u ((d : ℤ) - (x.1 : ℤ))
                - 2 * Fz u (d : ℤ) - 2 * Fz u (x.1 : ℤ))
            * Fz v (x.2.2.1 : ℤ))
    _ = _ := by rw [hsplit, hc0, hc1, hc2, hc3]

set_option maxHeartbeats 3200000 in

theorem groupG_eq_sum_lines (u : K) (hv0 : v ≠ 0) (M : ℕ) :
    cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.1.2 = k ∧ q.2.1 = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.1.2 = k ∧ q.2.2.2.1 = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ)) := by
  have hc0 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u (q.1.2 : ℤ) * Fz v ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_nat_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.1.2) (fun q => (q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show q.1.2 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hc1 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u (q.1.2 : ℤ) * Fz v ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_nat_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.1.2) (fun q => (q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show q.1.2 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hc2 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u (q.1.2 : ℤ) * Fz v (q.2.1 : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k ∧ q.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.1.2) (fun q => q.2.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show q.1.2 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show q.2.1 ≤ M
        omega)
  have hc3 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u (q.1.2 : ℤ) * Fz v (q.2.2.2.1 : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k ∧ q.2.2.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.1.2) (fun q => q.2.2.2.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show q.1.2 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tripleIdx_C3Collapse2 hq
        show q.2.2.2.1 ≤ M
        omega)
  have hsplit : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K) * Fz u (q.1.2 : ℤ)
            * (Fz v ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz v ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))
                - 2 * Fz v (q.2.1 : ℤ) - 2 * Fz v (q.2.2.2.1 : ℤ)))
      = (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u (q.1.2 : ℤ) * Fz v ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u (q.1.2 : ℤ) * Fz v ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
        - 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u (q.1.2 : ℤ) * Fz v (q.2.1 : ℤ))
        - 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u (q.1.2 : ℤ) * Fz v (q.2.2.2.1 : ℤ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  calc cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M
      = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i),
          (d : K) * (x.1 : K) * (x.2.2.1 : K) * Fz u (d : ℤ)
            * (Fz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + Fz v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
                - 2 * Fz v (x.1 : ℤ) - 2 * Fz v (x.2.2.1 : ℤ)) :=
        cauchyMulIntTriple_xvv_eq_sum_Fz u hv0 M
    _ = ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
          fun p => Sols (M - p.1),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K) * Fz u (q.1.2 : ℤ)
              * (Fz v ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz v ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))
                  - 2 * Fz v (q.2.1 : ℤ) - 2 * Fz v (q.2.2.2.1 : ℤ)) :=
        sum_Ico_divisors_Sols_eq_sigma M
          (fun i d x => (d : K) * (x.1 : K) * (x.2.2.1 : K) * Fz u (d : ℤ)
            * (Fz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + Fz v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
                - 2 * Fz v (x.1 : ℤ) - 2 * Fz v (x.2.2.1 : ℤ)))
    _ = _ := by rw [hsplit, hc0, hc1, hc2, hc3]

end Triples

section CrossInterior

theorem groupD_cross_diffsq_distrib (hu0 : u ≠ 0) (hv0 : v ≠ 0) (M : ℕ) :
    ∑ a ∈ Finset.Ico 1 M,
        (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
          * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
              (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)
      = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ x ∈ Sols (M - a),
          (d : K) * (x.1 : K) * (x.2.2.1 : K)
            * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ))
            * ((Fz u (x.1 : ℤ) - Fz v (x.1 : ℤ))
                * (Fz u (x.2.2.1 : ℤ) - Fz v (x.2.2.1 : ℤ))) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [xCoeff_mul_add_xCoeff_mul_inv hu0 hv0 a,
    cauchyMulInt_eq_sum_Sols (f := fun i => xDivTerm u i - xDivTerm v i)
      (g := fun i => xDivTerm u i - xDivTerm v i) (M - a)
      (fun i hi => by
        show xCoeffFull u i - xCoeffFull v i
            = ∑ b ∈ i.divisors, (xDivTerm u b - xDivTerm v b)
        rw [xCoeffFull_of_pos u hi, xCoeffFull_of_pos v hi, xCoeff, xCoeff,
          ← Finset.sum_sub_distrib])
      (fun i hi => by
        show xCoeffFull u i - xCoeffFull v i
            = ∑ b ∈ i.divisors, (xDivTerm u b - xDivTerm v b)
        rw [xCoeffFull_of_pos u hi, xCoeffFull_of_pos v hi, xCoeff, xCoeff,
          ← Finset.sum_sub_distrib]),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [xDivTerm_eq_mul_Fz]
  ring

end CrossInterior

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "cauchyMulInt xCoeffFull_of_pos cauchyMulInt_eq_sum_Sols Fz Gz xDivTerm_eq_mul_Fz tent Fz_natAbs add_le_of_mem_Sols sum_mul_Fz_eq_sum_lines_nat sum_mul_Fz_eq_sum_lines_int cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun b a₄ curve xDivTerm xCoeff addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex ks17_B_exports ks17_C2_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section Flatten

theorem sum_Sols_range_range_eq_sigma {β : Type*} [AddCommMonoid β] (M : ℕ)
    (f : ℕ × ℕ × ℕ × ℕ → ℕ → ℕ → β) :
    ∑ x ∈ Sols M, ∑ i ∈ Finset.range x.1, ∑ i' ∈ Finset.range x.2.2.1, f x i i'
      = ∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1,
          f q.1.1 q.1.2 q.2 :=
  calc ∑ x ∈ Sols M, ∑ i ∈ Finset.range x.1, ∑ i' ∈ Finset.range x.2.2.1, f x i i'
      = ∑ p ∈ (Sols M).sigma fun x => Finset.range x.1,
          ∑ i' ∈ Finset.range p.1.2.2.1, f p.1 p.2 i' :=
        Finset.sum_sigma' (Sols M) (fun x => Finset.range x.1)
          (fun x i => ∑ i' ∈ Finset.range x.2.2.1, f x i i')
    _ = ∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1,
          f q.1.1 q.1.2 q.2 :=
        Finset.sum_sigma' ((Sols M).sigma fun x => Finset.range x.1)
          (fun p => Finset.range p.1.2.2.1) (fun p i' => f p.1 p.2 i')

theorem sum_nest3_eq_sigma {β : Type*} [AddCommMonoid β] (S : Finset ℕ) (T : ℕ → Finset ℕ)
    (U : ℕ → ℕ → Finset ℕ) (f : ℕ → ℕ → ℕ → β) :
    ∑ d ∈ S, ∑ j ∈ T d, ∑ l ∈ U d j, f d j l
      = ∑ q ∈ (S.sigma T).sigma fun p => U p.1 p.2, f q.1.1 q.1.2 q.2 :=
  calc ∑ d ∈ S, ∑ j ∈ T d, ∑ l ∈ U d j, f d j l
      = ∑ p ∈ S.sigma T, ∑ l ∈ U p.1 p.2, f p.1 p.2 l :=
        Finset.sum_sigma' S T (fun d j => ∑ l ∈ U d j, f d j l)
    _ = ∑ q ∈ (S.sigma T).sigma fun p => U p.1 p.2, f q.1.1 q.1.2 q.2 :=
        Finset.sum_sigma' (S.sigma T) (fun p => U p.1 p.2) (fun p l => f p.1 p.2 l)

theorem sum_nest4_eq_sigma {β : Type*} [AddCommMonoid β] (S : Finset ℕ) (T : ℕ → Finset ℕ)
    (U : ℕ → ℕ → Finset ℕ) (V : ℕ → ℕ → ℕ → Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → β) :
    ∑ d ∈ S, ∑ j ∈ T d, ∑ l ∈ U d j, ∑ m ∈ V d j l, f d j l m
      = ∑ q ∈ ((S.sigma T).sigma fun p => U p.1 p.2).sigma fun r => V r.1.1 r.1.2 r.2,
          f q.1.1.1 q.1.1.2 q.1.2 q.2 :=
  calc ∑ d ∈ S, ∑ j ∈ T d, ∑ l ∈ U d j, ∑ m ∈ V d j l, f d j l m
      = ∑ q ∈ (S.sigma T).sigma fun p => U p.1 p.2, ∑ m ∈ V q.1.1 q.1.2 q.2, f q.1.1 q.1.2 q.2 m :=
        sum_nest3_eq_sigma S T U (fun d j l => ∑ m ∈ V d j l, f d j l m)
    _ = ∑ q ∈ ((S.sigma T).sigma fun p => U p.1 p.2).sigma fun r => V r.1.1 r.1.2 r.2,
          f q.1.1.1 q.1.1.2 q.1.2 q.2 :=
        Finset.sum_sigma' ((S.sigma T).sigma fun p => U p.1 p.2)
          (fun r => V r.1.1 r.1.2 r.2) (fun r m => f r.1.1 r.1.2 r.2 m)

private theorem bounds_of_mem_crossIdx_C3Collapse3 {M : ℕ}
    {q : Σ _ : (Σ _ : ℕ × ℕ × ℕ × ℕ, ℕ), ℕ}
    (hq : q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1) :
    q.1.2 < q.1.1.1 ∧ q.2 < q.1.1.2.2.1 ∧ q.1.1.1 + q.1.1.2.2.1 ≤ M := by
  have h1 := Finset.mem_sigma.mp hq
  have h2 := Finset.mem_sigma.mp h1.1
  exact ⟨Finset.mem_range.mp h2.2, Finset.mem_range.mp h1.2, add_le_of_mem_Sols h2.1⟩

private theorem le_of_mem_divisors_C3Collapse3 {d M : ℕ} (h : d ∈ M.divisors) : d ≤ M := by
  obtain ⟨h1, h2⟩ := Nat.mem_divisors.mp h
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1

end Flatten

section GroupA

set_option maxHeartbeats 6400000 in

theorem groupA_eq_sum_lines (u v : K) (M : ℕ) :
    ∑ x ∈ Sols M, ∑ i ∈ Finset.range x.1, ∑ i' ∈ Finset.range x.2.2.1,
        (x.1 : K) * (x.2.2.1 : K) *
          (Fz u ((i : ℤ) + i' + 1) * Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i')
            - Fz u ((i : ℤ) + i' + 1 - x.2.2.1) * Fz v ((i : ℤ) + i' + 1 - x.1)
            + 2 * (Fz u ((i : ℤ) + i' + 1) - Fz u ((i : ℤ) + i' + 1 - x.2.2.1))
            + 2 * (Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i')
                - Fz v ((i : ℤ) + i' + 1 - x.1)))
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
                fun p => Finset.range p.1.2.2.1).filter
                  (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k ∧
                    ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j),
              (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
                fun p => Finset.range p.1.2.2.1).filter
                  (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k ∧
                    ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j),
              (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + 2 * (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
                fun p => Finset.range p.1.2.2.1).filter
                  (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k),
              (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
              * Fz u (k : ℤ))
        - 2 * (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
                fun p => Finset.range p.1.2.2.1).filter
                  (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k),
              (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
              * Fz u (k : ℤ))
        + 2 * (∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
                fun p => Finset.range p.1.2.2.1).filter
                  (fun q => ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j),
              (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
              * Fz v (j : ℤ))
        - 2 * (∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
                fun p => Finset.range p.1.2.2.1).filter
                  (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j),
              (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
              * Fz v (j : ℤ)) := by
  have hc0 : (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
        fun p => Finset.range p.1.2.2.1,
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + q.2 + 1)
            * Fz v ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
              fun p => Finset.range p.1.2.2.1).filter
                (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k ∧
                  ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j),
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int
      (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1)
      (fun q => (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + q.2 + 1)
      (fun q => (q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2)
      (fun q hq => by
        obtain ⟨h1, h2, h3⟩ := bounds_of_mem_crossIdx_C3Collapse3 hq
        show ((q.1.2 : ℤ) + q.2 + 1).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3⟩ := bounds_of_mem_crossIdx_C3Collapse3 hq
        show ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs ≤ M
        omega)
  have hc1 : (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
        fun p => Finset.range p.1.2.2.1,
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1)
            * Fz v ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
              fun p => Finset.range p.1.2.2.1).filter
                (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k ∧
                  ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j),
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int
      (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1)
      (fun q => (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1)
      (fun q => (q.1.2 : ℤ) + q.2 + 1 - q.1.1.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3⟩ := bounds_of_mem_crossIdx_C3Collapse3 hq
        show ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3⟩ := bounds_of_mem_crossIdx_C3Collapse3 hq
        show ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs ≤ M
        omega)
  have hc2 : (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
        fun p => Finset.range p.1.2.2.1,
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K) * Fz u ((q.1.2 : ℤ) + q.2 + 1))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
              fun p => Finset.range p.1.2.2.1).filter
                (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k),
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1)
      (fun q => (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + q.2 + 1)
      (fun q hq => by
        obtain ⟨h1, h2, h3⟩ := bounds_of_mem_crossIdx_C3Collapse3 hq
        show ((q.1.2 : ℤ) + q.2 + 1).natAbs ≤ M
        omega)
  have hc3 : (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
        fun p => Finset.range p.1.2.2.1,
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K) * Fz u ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
              fun p => Finset.range p.1.2.2.1).filter
                (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k),
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1)
      (fun q => (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3⟩ := bounds_of_mem_crossIdx_C3Collapse3 hq
        show ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs ≤ M
        omega)
  have hc4 : (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
        fun p => Finset.range p.1.2.2.1,
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K)
            * Fz v ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2))
      = ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
              fun p => Finset.range p.1.2.2.1).filter
                (fun q => ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j),
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
            * Fz v (j : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1)
      (fun q => (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
      (fun q => (q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2)
      (fun q hq => by
        obtain ⟨h1, h2, h3⟩ := bounds_of_mem_crossIdx_C3Collapse3 hq
        show ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs ≤ M
        omega)
  have hc5 : (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
        fun p => Finset.range p.1.2.2.1,
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K) * Fz v ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1))
      = ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
              fun p => Finset.range p.1.2.2.1).filter
                (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j),
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
            * Fz v (j : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1)
      (fun q => (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + q.2 + 1 - q.1.1.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3⟩ := bounds_of_mem_crossIdx_C3Collapse3 hq
        show ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs ≤ M
        omega)
  have hsplit : (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
        fun p => Finset.range p.1.2.2.1,
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K) *
            (Fz u ((q.1.2 : ℤ) + q.2 + 1)
                * Fz v ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2)
              - Fz u ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1)
                  * Fz v ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1)
              + 2 * (Fz u ((q.1.2 : ℤ) + q.2 + 1)
                  - Fz u ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1))
              + 2 * (Fz v ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2)
                  - Fz v ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1))))
      = (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
            fun p => Finset.range p.1.2.2.1,
              (q.1.1.1 : K) * (q.1.1.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + q.2 + 1)
                * Fz v ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2))
        - (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
            fun p => Finset.range p.1.2.2.1,
              (q.1.1.1 : K) * (q.1.1.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1)
                * Fz v ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1))
        + 2 * (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
            fun p => Finset.range p.1.2.2.1,
              (q.1.1.1 : K) * (q.1.1.2.2.1 : K) * Fz u ((q.1.2 : ℤ) + q.2 + 1))
        - 2 * (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
            fun p => Finset.range p.1.2.2.1,
              (q.1.1.1 : K) * (q.1.1.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1))
        + 2 * (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
            fun p => Finset.range p.1.2.2.1,
              (q.1.1.1 : K) * (q.1.1.2.2.1 : K)
                * Fz v ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2))
        - 2 * (∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
            fun p => Finset.range p.1.2.2.1,
              (q.1.1.1 : K) * (q.1.1.2.2.1 : K)
                * Fz v ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  calc ∑ x ∈ Sols M, ∑ i ∈ Finset.range x.1, ∑ i' ∈ Finset.range x.2.2.1,
        (x.1 : K) * (x.2.2.1 : K) *
          (Fz u ((i : ℤ) + i' + 1) * Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i')
            - Fz u ((i : ℤ) + i' + 1 - x.2.2.1) * Fz v ((i : ℤ) + i' + 1 - x.1)
            + 2 * (Fz u ((i : ℤ) + i' + 1) - Fz u ((i : ℤ) + i' + 1 - x.2.2.1))
            + 2 * (Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i')
                - Fz v ((i : ℤ) + i' + 1 - x.1)))
      = ∑ q ∈ ((Sols M).sigma fun x => Finset.range x.1).sigma
          fun p => Finset.range p.1.2.2.1,
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K) *
              (Fz u ((q.1.2 : ℤ) + q.2 + 1)
                  * Fz v ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2)
                - Fz u ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1)
                    * Fz v ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1)
                + 2 * (Fz u ((q.1.2 : ℤ) + q.2 + 1)
                    - Fz u ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1))
                + 2 * (Fz v ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2)
                    - Fz v ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1))) :=
        sum_Sols_range_range_eq_sigma M
          (fun x i i' => (x.1 : K) * (x.2.2.1 : K) *
            (Fz u ((i : ℤ) + i' + 1) * Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i')
              - Fz u ((i : ℤ) + i' + 1 - x.2.2.1) * Fz v ((i : ℤ) + i' + 1 - x.1)
              + 2 * (Fz u ((i : ℤ) + i' + 1) - Fz u ((i : ℤ) + i' + 1 - x.2.2.1))
              + 2 * (Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i')
                  - Fz v ((i : ℤ) + i' + 1 - x.1))))
    _ = _ := by rw [hsplit, hc0, hc1, hc2, hc3, hc4, hc5]

end GroupA

section GroupB

set_option maxHeartbeats 6400000 in

theorem groupB_eq_sum_lines (u v : K) (M : ℕ) :
    ∑ d ∈ M.divisors, (d : K) *
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
                      * Fz v (l : ℤ) * Fz u (l' : ℤ)))
      = ((∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
              (d : K) * ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2))
          + (∑ k ∈ Finset.Icc 1 M,
              (∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
                  fun p => Finset.Ico 1 (p.1 + 1 - p.2)).filter (fun q => q.2 = k),
                (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 + 1 - q.1.2 - q.2 : ℕ) : K))
                * Fz u (k : ℤ))
          + (∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
                  fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j),
                (q.1.1 : K) * ((q.1.1 + 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K))
                * Fz v (j : ℤ))
          + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ (((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
                  fun p => Finset.Ico 1 p.2).sigma
                    fun r => Finset.Ico 1 (r.1.1 + 1 - r.1.2)).filter
                      (fun q => q.2 = k ∧ q.1.2 = j),
                (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K)
                  * ((q.1.1.1 + 1 - q.1.1.2 - q.2 : ℕ) : K))
                * Fz u (k : ℤ) * Fz v (j : ℤ)))
        - ((∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
              (d : K) * ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2))
          + (∑ k ∈ Finset.Icc 1 M,
              (∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma
                  fun p => Finset.Ico 1 (p.1 - 1 - p.2)).filter (fun q => q.2 = k),
                (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 - 1 - q.1.2 - q.2 : ℕ) : K))
                * Fz u (k : ℤ))
          + (∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma
                  fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j),
                (q.1.1 : K) * ((q.1.1 - 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K))
                * Fz v (j : ℤ))
          + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ (((M.divisors.sigma fun d => Finset.range d).sigma
                  fun p => Finset.Ico 1 p.2).sigma
                    fun r => Finset.Ico 1 (r.1.1 - 1 - r.1.2)).filter
                      (fun q => q.2 = k ∧ q.1.2 = j),
                (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K)
                  * ((q.1.1.1 - 1 - q.1.1.2 - q.2 : ℕ) : K))
                * Fz u (k : ℤ) * Fz v (j : ℤ))) := by

  have hUp : (∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
        (d : K) * ((j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j),
          ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
              fun p => Finset.Ico 1 (p.1 + 1 - p.2)).filter (fun q => q.2 = k),
            (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 + 1 - q.1.2 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) :=
    calc ∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
          (d : K) * ((j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j),
            ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ)))
        = ∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d, ∑ l ∈ Finset.Ico 1 (d + 1 - j),
            (d : K) * (j : K) ^ 2 * ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun j _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ q ∈ (M.divisors.sigma fun d => Finset.Icc 1 d).sigma
            fun p => Finset.Ico 1 (p.1 + 1 - p.2),
              (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 + 1 - q.1.2 - q.2 : ℕ) : K)
                * Fz u (q.2 : ℤ) :=
          sum_nest3_eq_sigma M.divisors (fun d => Finset.Icc 1 d)
            (fun d j => Finset.Ico 1 (d + 1 - j))
            (fun d j l => (d : K) * (j : K) ^ 2 * ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_nat
            ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
              fun p => Finset.Ico 1 (p.1 + 1 - p.2))
            (fun q => (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 + 1 - q.1.2 - q.2 : ℕ) : K))
            (fun q => q.2)
            (fun q hq => by
              have h1 := Finset.mem_sigma.mp hq
              have h2 := Finset.mem_sigma.mp h1.1
              have h3 := le_of_mem_divisors_C3Collapse3 h2.1
              have h4 := Finset.mem_Icc.mp h2.2
              have h5 := Finset.mem_Ico.mp h1.2
              show q.2 ≤ M
              omega)

  have hUm : (∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
        (d : K) * ((j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j),
          ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma
              fun p => Finset.Ico 1 (p.1 - 1 - p.2)).filter (fun q => q.2 = k),
            (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 - 1 - q.1.2 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) :=
    calc ∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
          (d : K) * ((j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j),
            ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ)))
        = ∑ d ∈ M.divisors, ∑ j ∈ Finset.range d, ∑ l ∈ Finset.Ico 1 (d - 1 - j),
            (d : K) * (j : K) ^ 2 * ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun j _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ q ∈ (M.divisors.sigma fun d => Finset.range d).sigma
            fun p => Finset.Ico 1 (p.1 - 1 - p.2),
              (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 - 1 - q.1.2 - q.2 : ℕ) : K)
                * Fz u (q.2 : ℤ) :=
          sum_nest3_eq_sigma M.divisors (fun d => Finset.range d)
            (fun d j => Finset.Ico 1 (d - 1 - j))
            (fun d j l => (d : K) * (j : K) ^ 2 * ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_nat
            ((M.divisors.sigma fun d => Finset.range d).sigma
              fun p => Finset.Ico 1 (p.1 - 1 - p.2))
            (fun q => (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 - 1 - q.1.2 - q.2 : ℕ) : K))
            (fun q => q.2)
            (fun q hq => by
              have h1 := Finset.mem_sigma.mp hq
              have h2 := Finset.mem_sigma.mp h1.1
              have h3 := le_of_mem_divisors_C3Collapse3 h2.1
              have h4 := Finset.mem_range.mp h2.2
              have h5 := Finset.mem_Ico.mp h1.2
              show q.2 ≤ M
              omega)

  have hVp : (∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
        (d : K) * (((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
          ((j - l : ℕ) : K) * Fz v (l : ℤ))))
      = ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
              fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j),
            (q.1.1 : K) * ((q.1.1 + 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K))
            * Fz v (j : ℤ) :=
    calc ∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
          (d : K) * (((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
            ((j - l : ℕ) : K) * Fz v (l : ℤ)))
        = ∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d, ∑ l ∈ Finset.Ico 1 j,
            (d : K) * ((d + 1 - j : ℕ) : K) ^ 2 * ((j - l : ℕ) : K) * Fz v (l : ℤ) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun j _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ q ∈ (M.divisors.sigma fun d => Finset.Icc 1 d).sigma
            fun p => Finset.Ico 1 p.2,
              (q.1.1 : K) * ((q.1.1 + 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K)
                * Fz v (q.2 : ℤ) :=
          sum_nest3_eq_sigma M.divisors (fun d => Finset.Icc 1 d)
            (fun _ j => Finset.Ico 1 j)
            (fun d j l => (d : K) * ((d + 1 - j : ℕ) : K) ^ 2 * ((j - l : ℕ) : K)
              * Fz v (l : ℤ))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_nat
            ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 p.2)
            (fun q => (q.1.1 : K) * ((q.1.1 + 1 - q.1.2 : ℕ) : K) ^ 2
              * ((q.1.2 - q.2 : ℕ) : K))
            (fun q => q.2)
            (fun q hq => by
              have h1 := Finset.mem_sigma.mp hq
              have h2 := Finset.mem_sigma.mp h1.1
              have h3 := le_of_mem_divisors_C3Collapse3 h2.1
              have h4 := Finset.mem_Icc.mp h2.2
              have h5 := Finset.mem_Ico.mp h1.2
              show q.2 ≤ M
              omega)

  have hVm : (∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
        (d : K) * (((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
          ((j - l : ℕ) : K) * Fz v (l : ℤ))))
      = ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma
              fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j),
            (q.1.1 : K) * ((q.1.1 - 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K))
            * Fz v (j : ℤ) :=
    calc ∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
          (d : K) * (((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
            ((j - l : ℕ) : K) * Fz v (l : ℤ)))
        = ∑ d ∈ M.divisors, ∑ j ∈ Finset.range d, ∑ l ∈ Finset.Ico 1 j,
            (d : K) * ((d - 1 - j : ℕ) : K) ^ 2 * ((j - l : ℕ) : K) * Fz v (l : ℤ) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun j _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ q ∈ (M.divisors.sigma fun d => Finset.range d).sigma
            fun p => Finset.Ico 1 p.2,
              (q.1.1 : K) * ((q.1.1 - 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K)
                * Fz v (q.2 : ℤ) :=
          sum_nest3_eq_sigma M.divisors (fun d => Finset.range d)
            (fun _ j => Finset.Ico 1 j)
            (fun d j l => (d : K) * ((d - 1 - j : ℕ) : K) ^ 2 * ((j - l : ℕ) : K)
              * Fz v (l : ℤ))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_nat
            ((M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 p.2)
            (fun q => (q.1.1 : K) * ((q.1.1 - 1 - q.1.2 : ℕ) : K) ^ 2
              * ((q.1.2 - q.2 : ℕ) : K))
            (fun q => q.2)
            (fun q hq => by
              have h1 := Finset.mem_sigma.mp hq
              have h2 := Finset.mem_sigma.mp h1.1
              have h3 := le_of_mem_divisors_C3Collapse3 h2.1
              have h4 := Finset.mem_range.mp h2.2
              have h5 := Finset.mem_Ico.mp h1.2
              show q.2 ≤ M
              omega)

  have hWp : (∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
        (d : K) * (∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j),
          ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K)
            * Fz v (l : ℤ) * Fz u (l' : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
              fun p => Finset.Ico 1 p.2).sigma
                fun r => Finset.Ico 1 (r.1.1 + 1 - r.1.2)).filter
                  (fun q => q.2 = k ∧ q.1.2 = j),
            (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K)
              * ((q.1.1.1 + 1 - q.1.1.2 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    calc ∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
          (d : K) * (∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j),
            ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K)
              * Fz v (l : ℤ) * Fz u (l' : ℤ))
        = ∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d, ∑ l ∈ Finset.Ico 1 j,
            ∑ l' ∈ Finset.Ico 1 (d + 1 - j),
              (d : K) * ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K)
                * Fz u (l' : ℤ) * Fz v (l : ℤ) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun j _ => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun l' _ => by ring
      _ = ∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
            fun p => Finset.Ico 1 p.2).sigma fun r => Finset.Ico 1 (r.1.1 + 1 - r.1.2),
              (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K)
                * ((q.1.1.1 + 1 - q.1.1.2 - q.2 : ℕ) : K)
                * Fz u (q.2 : ℤ) * Fz v (q.1.2 : ℤ) :=
          sum_nest4_eq_sigma M.divisors (fun d => Finset.Icc 1 d) (fun _ j => Finset.Ico 1 j)
            (fun d j _ => Finset.Ico 1 (d + 1 - j))
            (fun d j l l' => (d : K) * ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K)
              * Fz u (l' : ℤ) * Fz v (l : ℤ))
      _ = _ :=
          sum_mul_Fz_Fz_eq_sum_lines_nat
            (((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
              fun p => Finset.Ico 1 p.2).sigma fun r => Finset.Ico 1 (r.1.1 + 1 - r.1.2))
            (fun q => (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K)
              * ((q.1.1.1 + 1 - q.1.1.2 - q.2 : ℕ) : K))
            (fun q => q.2) (fun q => q.1.2)
            (fun q hq => by
              have h1 := Finset.mem_sigma.mp hq
              have h2 := Finset.mem_sigma.mp h1.1
              have h3 := Finset.mem_sigma.mp h2.1
              have h4 := le_of_mem_divisors_C3Collapse3 h3.1
              have h5 := Finset.mem_Icc.mp h3.2
              have h6 := Finset.mem_Ico.mp h2.2
              have h7 := Finset.mem_Ico.mp h1.2
              show q.2 ≤ M
              omega)
            (fun q hq => by
              have h1 := Finset.mem_sigma.mp hq
              have h2 := Finset.mem_sigma.mp h1.1
              have h3 := Finset.mem_sigma.mp h2.1
              have h4 := le_of_mem_divisors_C3Collapse3 h3.1
              have h5 := Finset.mem_Icc.mp h3.2
              have h6 := Finset.mem_Ico.mp h2.2
              have h7 := Finset.mem_Ico.mp h1.2
              show q.1.2 ≤ M
              omega)

  have hWm : (∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
        (d : K) * (∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j),
          ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K)
            * Fz v (l : ℤ) * Fz u (l' : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((M.divisors.sigma fun d => Finset.range d).sigma
              fun p => Finset.Ico 1 p.2).sigma
                fun r => Finset.Ico 1 (r.1.1 - 1 - r.1.2)).filter
                  (fun q => q.2 = k ∧ q.1.2 = j),
            (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K)
              * ((q.1.1.1 - 1 - q.1.1.2 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    calc ∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
          (d : K) * (∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j),
            ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K)
              * Fz v (l : ℤ) * Fz u (l' : ℤ))
        = ∑ d ∈ M.divisors, ∑ j ∈ Finset.range d, ∑ l ∈ Finset.Ico 1 j,
            ∑ l' ∈ Finset.Ico 1 (d - 1 - j),
              (d : K) * ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K)
                * Fz u (l' : ℤ) * Fz v (l : ℤ) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun j _ => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun l' _ => by ring
      _ = ∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma
            fun p => Finset.Ico 1 p.2).sigma fun r => Finset.Ico 1 (r.1.1 - 1 - r.1.2),
              (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K)
                * ((q.1.1.1 - 1 - q.1.1.2 - q.2 : ℕ) : K)
                * Fz u (q.2 : ℤ) * Fz v (q.1.2 : ℤ) :=
          sum_nest4_eq_sigma M.divisors (fun d => Finset.range d) (fun _ j => Finset.Ico 1 j)
            (fun d j _ => Finset.Ico 1 (d - 1 - j))
            (fun d j l l' => (d : K) * ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K)
              * Fz u (l' : ℤ) * Fz v (l : ℤ))
      _ = _ :=
          sum_mul_Fz_Fz_eq_sum_lines_nat
            (((M.divisors.sigma fun d => Finset.range d).sigma
              fun p => Finset.Ico 1 p.2).sigma fun r => Finset.Ico 1 (r.1.1 - 1 - r.1.2))
            (fun q => (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K)
              * ((q.1.1.1 - 1 - q.1.1.2 - q.2 : ℕ) : K))
            (fun q => q.2) (fun q => q.1.2)
            (fun q hq => by
              have h1 := Finset.mem_sigma.mp hq
              have h2 := Finset.mem_sigma.mp h1.1
              have h3 := Finset.mem_sigma.mp h2.1
              have h4 := le_of_mem_divisors_C3Collapse3 h3.1
              have h5 := Finset.mem_range.mp h3.2
              have h6 := Finset.mem_Ico.mp h2.2
              have h7 := Finset.mem_Ico.mp h1.2
              show q.2 ≤ M
              omega)
            (fun q hq => by
              have h1 := Finset.mem_sigma.mp hq
              have h2 := Finset.mem_sigma.mp h1.1
              have h3 := Finset.mem_sigma.mp h2.1
              have h4 := le_of_mem_divisors_C3Collapse3 h3.1
              have h5 := Finset.mem_range.mp h3.2
              have h6 := Finset.mem_Ico.mp h2.2
              have h7 := Finset.mem_Ico.mp h1.2
              show q.1.2 ≤ M
              omega)

  have hsplitP : (∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
        (d : K) * ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2
          + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j),
              ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ))
          + ((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
              ((j - l : ℕ) : K) * Fz v (l : ℤ))
          + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j),
              ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K)
                * Fz v (l : ℤ) * Fz u (l' : ℤ)))
      = (∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
            (d : K) * ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2))
        + (∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
            (d : K) * ((j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j),
              ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ))))
        + (∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
            (d : K) * (((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
              ((j - l : ℕ) : K) * Fz v (l : ℤ))))
        + (∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
            (d : K) * (∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j),
              ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K)
                * Fz v (l : ℤ) * Fz u (l' : ℤ))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring

  have hsplitM : (∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
        (d : K) * ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2
          + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j),
              ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ))
          + ((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
              ((j - l : ℕ) : K) * Fz v (l : ℤ))
          + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j),
              ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K)
                * Fz v (l : ℤ) * Fz u (l' : ℤ)))
      = (∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
            (d : K) * ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2))
        + (∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
            (d : K) * ((j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j),
              ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ))))
        + (∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
            (d : K) * (((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
              ((j - l : ℕ) : K) * Fz v (l : ℤ))))
        + (∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
            (d : K) * (∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j),
              ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K)
                * Fz v (l : ℤ) * Fz u (l' : ℤ))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
  calc ∑ d ∈ M.divisors, (d : K) *
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
                      * Fz v (l : ℤ) * Fz u (l' : ℤ)))
      = (∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
            (d : K) * ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2
              + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j),
                  ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ))
              + ((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
                  ((j - l : ℕ) : K) * Fz v (l : ℤ))
              + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j),
                  ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K)
                    * Fz v (l : ℤ) * Fz u (l' : ℤ)))
        - (∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
            (d : K) * ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2
              + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j),
                  ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ))
              + ((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j,
                  ((j - l : ℕ) : K) * Fz v (l : ℤ))
              + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j),
                  ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K)
                    * Fz v (l : ℤ) * Fz u (l' : ℤ))) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun d _ => by
          rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by rw [hsplitP, hsplitM, hUp, hVp, hWp, hUm, hVm, hWm]

end GroupB

end TateCurve

theorem solution :

    (∀ {β : Type u_2} [AddCommMonoid β] (S : Finset ℕ) (T : ℕ → Finset ℕ)
    (U : ℕ → ℕ → Finset ℕ) (f : ℕ → ℕ → ℕ → β),
      ∑ d ∈ S, ∑ j ∈ T d, ∑ l ∈ U d j, f d j l = ∑ q ∈ (S.sigma T).sigma fun p => U p.1 p.2, f q.1.1 q.1.2 q.2) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g h : α → ℕ)
    {N : ℕ} (hg : ∀ x ∈ S, g x ≤ N) (hh : ∀ x ∈ S, h x ≤ N),
      ∑ x ∈ S, w x * Fz u (g x : ℤ) * Fz v (h x : ℤ) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => g x = k ∧ h x = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g : α → ℕ)
    (h : α → ℤ) {N : ℕ} (hg : ∀ x ∈ S, g x ≤ N) (hh : ∀ x ∈ S, (h x).natAbs ≤ N),
      ∑ x ∈ S, w x * Fz u (g x : ℤ) * Fz v (h x) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => g x = k ∧ (h x).natAbs = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g : α → ℤ)
    (h : α → ℕ) {N : ℕ} (hg : ∀ x ∈ S, (g x).natAbs ≤ N) (hh : ∀ x ∈ S, h x ≤ N),
      ∑ x ∈ S, w x * Fz u (g x) * Fz v (h x : ℤ) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => (g x).natAbs = k ∧ h x = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g h : α → ℤ)
    {N : ℕ} (hg : ∀ x ∈ S, (g x).natAbs ≤ N) (hh : ∀ x ∈ S, (h x).natAbs ≤ N),
      ∑ x ∈ S, w x * Fz u (g x) * Fz v (h x) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => (g x).natAbs = k ∧ (h x).natAbs = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {β : Type u_2} [AddCommMonoid β] (M : ℕ)
    (f : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ → β),
      ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i), f i d x = ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), f q.1.1 q.1.2 q.2) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (v : K) (M : ℕ),
      ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1 = (∑ j ∈ Finset.Icc 1 M, (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = j), (x.1 : K) ^ 3 * (x.2.2.1 : K)) * Fz v (j : ℤ)) + ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ p ∈ ((Sols M).sigma fun x => Finset.Ico 1 x.1).filter (fun p => p.2 = k ∧ p.1.2.2.1 = j), (p.1.1 : K) * ((p.1.1 - p.2 : ℕ) : K) * (p.1.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {v : K} [CharZero K] (u : K) (hv0 : v ≠ 0) (hv1 : v ≠ 1) (M : ℕ),
      ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1) = (∑ k ∈ Finset.Icc 1 M, (∑ x ∈ (Sols M).filter (fun x => x.1 = k), (x.2.2.1 : K) ^ 3 * (x.1 : K)) * Fz u (k : ℤ)) + ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ p ∈ ((Sols M).sigma fun x => Finset.Ico 1 x.2.2.1).filter (fun p => p.1.1 = k ∧ p.2 = j), (p.1.2.2.1 : K) * ((p.1.2.2.1 - p.2 : ℕ) : K) * (p.1.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (v : K) (M : ℕ),
      cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {v : K} (u : K) (hv0 : v ≠ 0) (M : ℕ),
      cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      cauchyMulInt (xCoeffFull u) (xCoeffFull v) M = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ x ∈ (Sols M).filter (fun x => x.1 = k ∧ x.2.2.1 = j), (x.1 : K) * (x.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u : K) (M : ℕ),
      cauchyMulInt a₄Coeff (xCoeffFull u) M = ∑ k ∈ Finset.Icc 1 M, (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = k), -((5 * x.1 ^ 3 : ℕ) : K) * (x.2.2.1 : K)) * Fz u (k : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      ∑ x ∈ Sols M, ∑ i ∈ Finset.range x.1, ∑ i' ∈ Finset.range x.2.2.1, (x.1 : K) * (x.2.2.1 : K) * (Fz u ((i : ℤ) + i' + 1) * Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i') - Fz u ((i : ℤ) + i' + 1 - x.2.2.1) * Fz v ((i : ℤ) + i' + 1 - x.1) + 2 * (Fz u ((i : ℤ) + i' + 1) - Fz u ((i : ℤ) + i' + 1 - x.2.2.1)) + 2 * (Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i') - Fz v ((i : ℤ) + i' + 1 - x.1))) = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k ∧ ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k ∧ ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz u (k : ℤ)) + 2 * (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz v (j : ℤ)) - 2 * (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz v (j : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2 + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j), ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ)) + ((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j), ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) - ∑ j ∈ Finset.range d, ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2 + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j), ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ)) + ((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j), ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) = ((∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d, (d : K) * ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 (p.1 + 1 - p.2)).filter (fun q => q.2 = k), (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 + 1 - q.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j), (q.1.1 : K) * ((q.1.1 + 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K)) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 p.2).sigma fun r => Finset.Ico 1 (r.1.1 + 1 - r.1.2)).filter (fun q => q.2 = k ∧ q.1.2 = j), (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K) * ((q.1.1.1 + 1 - q.1.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ))) - ((∑ d ∈ M.divisors, ∑ j ∈ Finset.range d, (d : K) * ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 (p.1 - 1 - p.2)).filter (fun q => q.2 = k), (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 - 1 - q.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j), (q.1.1 : K) * ((q.1.1 - 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K)) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 p.2).sigma fun r => Finset.Ico 1 (r.1.1 - 1 - r.1.2)).filter (fun q => q.2 = k ∧ q.1.2 = j), (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K) * ((q.1.1.1 - 1 - q.1.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - a) = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ x ∈ Sols (M - a), (d : K) * (x.1 : K) * (x.2.2.1 : K) * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ)) * ((Fz u (x.1 : ℤ) - Fz v (x.1 : ℤ)) * (Fz u (x.2.2.1 : ℤ) - Fz v (x.2.2.1 : ℤ)))) :=
  ⟨TateCurve.sum_nest3_eq_sigma,
   TateCurve.sum_mul_Fz_Fz_eq_sum_lines_nat,
   TateCurve.sum_mul_Fz_Fz_eq_sum_lines_nat_int,
   TateCurve.sum_mul_Fz_Fz_eq_sum_lines_int_nat,
   TateCurve.sum_mul_Fz_Fz_eq_sum_lines_int,
   TateCurve.sum_Ico_divisors_Sols_eq_sigma,
   TateCurve.groupE1_eq_sum_lines,
   TateCurve.groupE2_eq_sum_lines,
   TateCurve.groupF_eq_sum_lines,
   TateCurve.groupG_eq_sum_lines,
   TateCurve.groupH_eq_sum_lines,
   TateCurve.groupI_eq_sum_lines,
   TateCurve.groupA_eq_sum_lines,
   TateCurve.groupB_eq_sum_lines,
   TateCurve.groupD_cross_diffsq_distrib⟩

end S_TateCurve_ks17_C3_exports
end P2MW
export P2MW.S_TateCurve_ks17_C3_exports (solution)
