-- Prove2me | solution 1 for TateCurve.ks17_D3_exports
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/903956dd-dfc3-5663-bb80-51d705d0b17b

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab
import Theorems.Thm_TateCurve_ks17_C2_exports
import Theorems.Thm_TateCurve_ks17_C3_exports
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_ks17_D3_exports

open scoped NNReal
p2m_open "TateCurve P2MW.S_TateCurve_ks17_D3_exports.TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset"

universe u_1 u_2

namespace TateCurve
p2m_export "TateCurve" "cauchyMulInt Fz Fz_mul_Fz tent tent_eq_sq_add_sum_Ico add_le_of_mem_Sols sum_mul_Fz_eq_sum_lines_nat sum_mul_Fz_eq_sum_lines_int xCoeffFull a₄Coeff a₆Coeff term b curve xDivTerm xCoeff addDefectSumCoeff cauchyMulIntTriple ks17_C2_exports ks17_C3_exports"
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

namespace TateCurve
p2m_export "TateCurve" "cauchyMulInt Fz Fz_mul_Fz tent tent_eq_sq_add_sum_Ico add_le_of_mem_Sols sum_mul_Fz_eq_sum_lines_nat sum_mul_Fz_eq_sum_lines_int xCoeffFull a₄Coeff a₆Coeff term b curve xDivTerm xCoeff addDefectSumCoeff cauchyMulIntTriple ks17_C2_exports ks17_C3_exports"
p2m_open "TateCurve"

theorem sum_nest3_eq_sigma : ∀ {β : Type u_2} [AddCommMonoid β] (S : Finset ℕ) (T : ℕ → Finset ℕ)
    (U : ℕ → ℕ → Finset ℕ) (f : ℕ → ℕ → ℕ → β),
      ∑ d ∈ S, ∑ j ∈ T d, ∑ l ∈ U d j, f d j l = ∑ q ∈ (S.sigma T).sigma fun p => U p.1 p.2, f q.1.1 q.1.2 q.2 :=
  TateCurve.ks17_C3_exports.{0, u_2}.1

theorem sum_mul_Fz_Fz_eq_sum_lines_nat : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g h : α → ℕ)
    {N : ℕ} (hg : ∀ x ∈ S, g x ≤ N) (hh : ∀ x ∈ S, h x ≤ N),
      ∑ x ∈ S, w x * Fz u (g x : ℤ) * Fz v (h x : ℤ) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => g x = k ∧ h x = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ) :=
  TateCurve.ks17_C3_exports.{u_1, u_2}.2.1

theorem sum_mul_Fz_Fz_eq_sum_lines_nat_int : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g : α → ℕ)
    (h : α → ℤ) {N : ℕ} (hg : ∀ x ∈ S, g x ≤ N) (hh : ∀ x ∈ S, (h x).natAbs ≤ N),
      ∑ x ∈ S, w x * Fz u (g x : ℤ) * Fz v (h x) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => g x = k ∧ (h x).natAbs = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ) :=
  TateCurve.ks17_C3_exports.{u_1, u_2}.2.2.1

theorem sum_mul_Fz_Fz_eq_sum_lines_int_nat : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g : α → ℤ)
    (h : α → ℕ) {N : ℕ} (hg : ∀ x ∈ S, (g x).natAbs ≤ N) (hh : ∀ x ∈ S, h x ≤ N),
      ∑ x ∈ S, w x * Fz u (g x) * Fz v (h x : ℤ) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => (g x).natAbs = k ∧ h x = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ) :=
  TateCurve.ks17_C3_exports.{u_1, u_2}.2.2.2.1

theorem sum_mul_Fz_Fz_eq_sum_lines_int : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g h : α → ℤ)
    {N : ℕ} (hg : ∀ x ∈ S, (g x).natAbs ≤ N) (hh : ∀ x ∈ S, (h x).natAbs ≤ N),
      ∑ x ∈ S, w x * Fz u (g x) * Fz v (h x) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => (g x).natAbs = k ∧ (h x).natAbs = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ) :=
  TateCurve.ks17_C3_exports.{u_1, u_2}.2.2.2.2.1

theorem sum_Ico_divisors_Sols_eq_sigma : ∀ {β : Type u_2} [AddCommMonoid β] (M : ℕ)
    (f : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ → β),
      ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i), f i d x = ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), f q.1.1 q.1.2 q.2 :=
  TateCurve.ks17_C3_exports.{0, u_2}.2.2.2.2.2.1

theorem groupE1_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (v : K) (M : ℕ),
      ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1 = (∑ j ∈ Finset.Icc 1 M, (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = j), (x.1 : K) ^ 3 * (x.2.2.1 : K)) * Fz v (j : ℤ)) + ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ p ∈ ((Sols M).sigma fun x => Finset.Ico 1 x.1).filter (fun p => p.2 = k ∧ p.1.2.2.1 = j), (p.1.1 : K) * ((p.1.1 - p.2 : ℕ) : K) * (p.1.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ) :=
  TateCurve.ks17_C3_exports.{u_1, 0}.2.2.2.2.2.2.1

theorem groupE2_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {v : K} [CharZero K] (u : K) (hv0 : v ≠ 0) (hv1 : v ≠ 1) (M : ℕ),
      ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1) = (∑ k ∈ Finset.Icc 1 M, (∑ x ∈ (Sols M).filter (fun x => x.1 = k), (x.2.2.1 : K) ^ 3 * (x.1 : K)) * Fz u (k : ℤ)) + ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ p ∈ ((Sols M).sigma fun x => Finset.Ico 1 x.2.2.1).filter (fun p => p.1.1 = k ∧ p.2 = j), (p.1.2.2.1 : K) * ((p.1.2.2.1 - p.2 : ℕ) : K) * (p.1.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ) :=
  TateCurve.ks17_C3_exports.{u_1, 0}.2.2.2.2.2.2.2.1

theorem groupF_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (v : K) (M : ℕ),
      cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) :=
  TateCurve.ks17_C3_exports.{u_1, 0}.2.2.2.2.2.2.2.2.1

theorem groupG_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {v : K} (u : K) (hv0 : v ≠ 0) (M : ℕ),
      cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) :=
  TateCurve.ks17_C3_exports.{u_1, 0}.2.2.2.2.2.2.2.2.2.1

theorem groupH_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      cauchyMulInt (xCoeffFull u) (xCoeffFull v) M = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ x ∈ (Sols M).filter (fun x => x.1 = k ∧ x.2.2.1 = j), (x.1 : K) * (x.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ) :=
  TateCurve.ks17_C3_exports.{u_1, 0}.2.2.2.2.2.2.2.2.2.2.1

theorem groupI_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u : K) (M : ℕ),
      cauchyMulInt a₄Coeff (xCoeffFull u) M = ∑ k ∈ Finset.Icc 1 M, (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = k), -((5 * x.1 ^ 3 : ℕ) : K) * (x.2.2.1 : K)) * Fz u (k : ℤ) :=
  TateCurve.ks17_C3_exports.{u_1, 0}.2.2.2.2.2.2.2.2.2.2.2.1

theorem groupA_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      ∑ x ∈ Sols M, ∑ i ∈ Finset.range x.1, ∑ i' ∈ Finset.range x.2.2.1, (x.1 : K) * (x.2.2.1 : K) * (Fz u ((i : ℤ) + i' + 1) * Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i') - Fz u ((i : ℤ) + i' + 1 - x.2.2.1) * Fz v ((i : ℤ) + i' + 1 - x.1) + 2 * (Fz u ((i : ℤ) + i' + 1) - Fz u ((i : ℤ) + i' + 1 - x.2.2.1)) + 2 * (Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i') - Fz v ((i : ℤ) + i' + 1 - x.1))) = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k ∧ ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k ∧ ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz u (k : ℤ)) + 2 * (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz v (j : ℤ)) - 2 * (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz v (j : ℤ)) :=
  TateCurve.ks17_C3_exports.{u_1, 0}.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem groupB_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2 + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j), ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ)) + ((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j), ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) - ∑ j ∈ Finset.range d, ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2 + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j), ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ)) + ((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j), ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) = ((∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d, (d : K) * ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 (p.1 + 1 - p.2)).filter (fun q => q.2 = k), (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 + 1 - q.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j), (q.1.1 : K) * ((q.1.1 + 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K)) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 p.2).sigma fun r => Finset.Ico 1 (r.1.1 + 1 - r.1.2)).filter (fun q => q.2 = k ∧ q.1.2 = j), (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K) * ((q.1.1.1 + 1 - q.1.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ))) - ((∑ d ∈ M.divisors, ∑ j ∈ Finset.range d, (d : K) * ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 (p.1 - 1 - p.2)).filter (fun q => q.2 = k), (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 - 1 - q.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j), (q.1.1 : K) * ((q.1.1 - 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K)) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 p.2).sigma fun r => Finset.Ico 1 (r.1.1 - 1 - r.1.2)).filter (fun q => q.2 = k ∧ q.1.2 = j), (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K) * ((q.1.1.1 - 1 - q.1.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ))) :=
  TateCurve.ks17_C3_exports.{u_1, 0}.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem groupD_cross_diffsq_distrib : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - a) = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ x ∈ Sols (M - a), (d : K) * (x.1 : K) * (x.2.2.1 : K) * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ)) * ((Fz u (x.1 : ℤ) - Fz v (x.1 : ℤ)) * (Fz u (x.2.2.1 : ℤ) - Fz v (x.2.2.1 : ℤ))) :=
  TateCurve.ks17_C3_exports.{u_1, 0}.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "cauchyMulInt Fz Fz_mul_Fz tent tent_eq_sq_add_sum_Ico add_le_of_mem_Sols sum_mul_Fz_eq_sum_lines_nat sum_mul_Fz_eq_sum_lines_int xCoeffFull a₄Coeff a₆Coeff term b curve xDivTerm xCoeff addDefectSumCoeff cauchyMulIntTriple ks17_C2_exports ks17_C3_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section Bounds

private theorem le_of_mem_divisors_Collapse4 {d M : ℕ} (h : d ∈ M.divisors) : d ≤ M := by
  obtain ⟨h1, h2⟩ := Nat.mem_divisors.mp h
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1

private theorem bounds_of_mem_pairIdx_Collapse4 {M : ℕ} {q : Σ _ : ℕ, ℕ}
    (hq : q ∈ M.divisors.sigma fun d => Finset.Ico 1 d) :
    q.1 ≤ M ∧ q.2 < q.1 := by
  have h1 := Finset.mem_sigma.mp hq
  have h2 := le_of_mem_divisors_Collapse4 h1.1
  have h3 := Finset.mem_Ico.mp h1.2
  exact ⟨h2, h3.2⟩

private theorem bounds_of_mem_colIdx_Collapse4 {M : ℕ} {q : Σ _ : (Σ _ : ℕ, ℕ), ℕ}
    (hq : q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2) :
    q.1.1 ≤ M ∧ q.1.2 < q.1.1 ∧ q.2 < q.1.2 := by
  have h1 := Finset.mem_sigma.mp hq
  have h2 := bounds_of_mem_pairIdx_Collapse4 h1.1
  have h3 := Finset.mem_Ico.mp h1.2
  exact ⟨h2.1, h2.2, h3.2⟩

private theorem bounds_of_mem_diagIdx_Collapse4 {M : ℕ} {q : Σ _ : (Σ _ : ℕ, ℕ), ℕ}
    (hq : q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.1) :
    q.1.1 ≤ M ∧ q.1.2 < q.1.1 ∧ q.2 < q.1.1 := by
  have h1 := Finset.mem_sigma.mp hq
  have h2 := bounds_of_mem_pairIdx_Collapse4 h1.1
  have h3 := Finset.mem_Ico.mp h1.2
  exact ⟨h2.1, h2.2, h3.2⟩

end Bounds

section GroupC

set_option maxHeartbeats 12800000 in

theorem groupC_eq_sum_lines (u v : K) (M : ℕ) :
    ∑ d ∈ M.divisors, (d : K) *
        ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) *
            ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ)))
          + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) *
              ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ)))
          - 2 * ((d : K) ^ 2 * (d : K) ^ 2
              + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ))
              + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ))
              + ∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d,
                  ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ)))
      = ((∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.1 = j),
                (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2)
                * Fz v (j : ℤ))
          + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
              2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2))
          + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
                  fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = k ∧ q.1.1 = j),
                (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))
                * Fz u (k : ℤ) * Fz v (j : ℤ))
          + (∑ k ∈ Finset.Icc 1 M,
              (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
                  fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = k),
                2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)))
                * Fz u (k : ℤ)))
        + ((∑ k ∈ Finset.Icc 1 M,
              (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.1 = k),
                (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2)
                * Fz u (k : ℤ))
          + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
              2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2))
          + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
                  fun p => Finset.Ico 1 p.2).filter (fun q => q.1.1 = k ∧ q.2 = j),
                (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))
                * Fz u (k : ℤ) * Fz v (j : ℤ))
          + (∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
                  fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j),
                2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)))
                * Fz v (j : ℤ)))
        - 2 * ((∑ d ∈ M.divisors, (d : K) * ((d : K) ^ 2 * (d : K) ^ 2))
          + (∑ k ∈ Finset.Icc 1 M,
              (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.2 = k),
                (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K))
                * Fz u (k : ℤ))
          + (∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.2 = j),
                (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K))
                * Fz v (j : ℤ))
          + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
                  fun p => Finset.Ico 1 p.1).filter (fun q => q.2 = k ∧ q.1.2 = j),
                (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.1 - q.2 : ℕ) : K))
                * Fz u (k : ℤ) * Fz v (j : ℤ))) := by

  have hC1pv : (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
        (d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2 * Fz v (d : ℤ))
      = ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.1 = j),
            (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2)
            * Fz v (j : ℤ) :=
    calc ∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
          (d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2 * Fz v (d : ℤ)
        = ∑ q ∈ M.divisors.sigma fun d => Finset.Ico 1 d,
            (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2 * Fz v (q.1 : ℤ) :=
          Finset.sum_sigma' M.divisors (fun d => Finset.Ico 1 d)
            (fun d k => (d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2 * Fz v (d : ℤ))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_nat (M.divisors.sigma fun d => Finset.Ico 1 d)
            (fun q => (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2)
            (fun q => q.1)
            (fun q hq => by
              obtain ⟨h1, h2⟩ := bounds_of_mem_pairIdx_Collapse4 hq
              show q.1 ≤ M
              omega)

  have hC1mx : (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
        (d : K) * ((d - k : ℕ) : K)
          * (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ)) * Fz v (d : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
              fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = k ∧ q.1.1 = j),
            (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    calc ∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
          (d : K) * ((d - k : ℕ) : K)
            * (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ)) * Fz v (d : ℤ)
        = ∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d, ∑ l ∈ Finset.Ico 1 k,
            (d : K) * ((d - k : ℕ) : K) * ((k - l : ℕ) : K)
              * Fz u (l : ℤ) * Fz v (d : ℤ) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun k _ => by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).sigma
            fun p => Finset.Ico 1 p.2,
              (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)
                * Fz u (q.2 : ℤ) * Fz v (q.1.1 : ℤ) :=
          sum_nest3_eq_sigma M.divisors (fun d => Finset.Ico 1 d)
            (fun _ k => Finset.Ico 1 k)
            (fun d k l => (d : K) * ((d - k : ℕ) : K) * ((k - l : ℕ) : K)
              * Fz u (l : ℤ) * Fz v (d : ℤ))
      _ = _ :=
          sum_mul_Fz_Fz_eq_sum_lines_nat
            ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2)
            (fun q => (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))
            (fun q => q.2) (fun q => q.1.1)
            (fun q hq => by
              obtain ⟨h1, h2, h3⟩ := bounds_of_mem_colIdx_Collapse4 hq
              show q.2 ≤ M
              omega)
            (fun q hq => by
              obtain ⟨h1, h2, h3⟩ := bounds_of_mem_colIdx_Collapse4 hq
              show q.1.1 ≤ M
              omega)

  have hC1pu : (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
        2 * ((d : K) * ((d - k : ℕ) : K)
          * (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
              fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = k),
            2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)))
            * Fz u (k : ℤ) :=
    calc ∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
          2 * ((d : K) * ((d - k : ℕ) : K)
            * (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ)))
        = ∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d, ∑ l ∈ Finset.Ico 1 k,
            2 * ((d : K) * ((d - k : ℕ) : K) * ((k - l : ℕ) : K)) * Fz u (l : ℤ) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun k _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).sigma
            fun p => Finset.Ico 1 p.2,
              2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))
                * Fz u (q.2 : ℤ) :=
          sum_nest3_eq_sigma M.divisors (fun d => Finset.Ico 1 d)
            (fun _ k => Finset.Ico 1 k)
            (fun d k l => 2 * ((d : K) * ((d - k : ℕ) : K) * ((k - l : ℕ) : K))
              * Fz u (l : ℤ))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_nat
            ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2)
            (fun q => 2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)))
            (fun q => q.2)
            (fun q hq => by
              obtain ⟨h1, h2, h3⟩ := bounds_of_mem_colIdx_Collapse4 hq
              show q.2 ≤ M
              omega)

  have hC2pu : (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
        (d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2 * Fz u (d : ℤ))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.1 = k),
            (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2)
            * Fz u (k : ℤ) :=
    calc ∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
          (d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2 * Fz u (d : ℤ)
        = ∑ q ∈ M.divisors.sigma fun d => Finset.Ico 1 d,
            (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2 * Fz u (q.1 : ℤ) :=
          Finset.sum_sigma' M.divisors (fun d => Finset.Ico 1 d)
            (fun d k => (d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2 * Fz u (d : ℤ))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_nat (M.divisors.sigma fun d => Finset.Ico 1 d)
            (fun q => (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2)
            (fun q => q.1)
            (fun q hq => by
              obtain ⟨h1, h2⟩ := bounds_of_mem_pairIdx_Collapse4 hq
              show q.1 ≤ M
              omega)

  have hC2mx : (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
        (d : K) * ((d - k : ℕ) : K)
          * (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ)) * Fz u (d : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
              fun p => Finset.Ico 1 p.2).filter (fun q => q.1.1 = k ∧ q.2 = j),
            (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    calc ∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
          (d : K) * ((d - k : ℕ) : K)
            * (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ)) * Fz u (d : ℤ)
        = ∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d, ∑ l ∈ Finset.Ico 1 k,
            (d : K) * ((d - k : ℕ) : K) * ((k - l : ℕ) : K)
              * Fz u (d : ℤ) * Fz v (l : ℤ) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun k _ => by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).sigma
            fun p => Finset.Ico 1 p.2,
              (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)
                * Fz u (q.1.1 : ℤ) * Fz v (q.2 : ℤ) :=
          sum_nest3_eq_sigma M.divisors (fun d => Finset.Ico 1 d)
            (fun _ k => Finset.Ico 1 k)
            (fun d k l => (d : K) * ((d - k : ℕ) : K) * ((k - l : ℕ) : K)
              * Fz u (d : ℤ) * Fz v (l : ℤ))
      _ = _ :=
          sum_mul_Fz_Fz_eq_sum_lines_nat
            ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2)
            (fun q => (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))
            (fun q => q.1.1) (fun q => q.2)
            (fun q hq => by
              obtain ⟨h1, h2, h3⟩ := bounds_of_mem_colIdx_Collapse4 hq
              show q.1.1 ≤ M
              omega)
            (fun q hq => by
              obtain ⟨h1, h2, h3⟩ := bounds_of_mem_colIdx_Collapse4 hq
              show q.2 ≤ M
              omega)

  have hC2pv : (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
        2 * ((d : K) * ((d - k : ℕ) : K)
          * (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ))))
      = ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
              fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j),
            2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)))
            * Fz v (j : ℤ) :=
    calc ∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
          2 * ((d : K) * ((d - k : ℕ) : K)
            * (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ)))
        = ∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d, ∑ l ∈ Finset.Ico 1 k,
            2 * ((d : K) * ((d - k : ℕ) : K) * ((k - l : ℕ) : K)) * Fz v (l : ℤ) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun k _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).sigma
            fun p => Finset.Ico 1 p.2,
              2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))
                * Fz v (q.2 : ℤ) :=
          sum_nest3_eq_sigma M.divisors (fun d => Finset.Ico 1 d)
            (fun _ k => Finset.Ico 1 k)
            (fun d k l => 2 * ((d : K) * ((d - k : ℕ) : K) * ((k - l : ℕ) : K))
              * Fz v (l : ℤ))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_nat
            ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2)
            (fun q => 2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)))
            (fun q => q.2)
            (fun q hq => by
              obtain ⟨h1, h2, h3⟩ := bounds_of_mem_colIdx_Collapse4 hq
              show q.2 ≤ M
              omega)

  have hC3pu : (∑ d ∈ M.divisors,
        (d : K) * ((d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.2 = k),
            (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) :=
    calc ∑ d ∈ M.divisors,
          (d : K) * ((d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ)))
        = ∑ d ∈ M.divisors, ∑ l ∈ Finset.Ico 1 d,
            (d : K) * (d : K) ^ 2 * ((d - l : ℕ) : K) * Fz u (l : ℤ) :=
          Finset.sum_congr rfl fun d _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ q ∈ M.divisors.sigma fun d => Finset.Ico 1 d,
            (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K) * Fz u (q.2 : ℤ) :=
          Finset.sum_sigma' M.divisors (fun d => Finset.Ico 1 d)
            (fun d l => (d : K) * (d : K) ^ 2 * ((d - l : ℕ) : K) * Fz u (l : ℤ))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_nat (M.divisors.sigma fun d => Finset.Ico 1 d)
            (fun q => (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K))
            (fun q => q.2)
            (fun q hq => by
              obtain ⟨h1, h2⟩ := bounds_of_mem_pairIdx_Collapse4 hq
              show q.2 ≤ M
              omega)

  have hC3pv : (∑ d ∈ M.divisors,
        (d : K) * ((d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ))))
      = ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.2 = j),
            (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K))
            * Fz v (j : ℤ) :=
    calc ∑ d ∈ M.divisors,
          (d : K) * ((d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ)))
        = ∑ d ∈ M.divisors, ∑ l ∈ Finset.Ico 1 d,
            (d : K) * (d : K) ^ 2 * ((d - l : ℕ) : K) * Fz v (l : ℤ) :=
          Finset.sum_congr rfl fun d _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ q ∈ M.divisors.sigma fun d => Finset.Ico 1 d,
            (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K) * Fz v (q.2 : ℤ) :=
          Finset.sum_sigma' M.divisors (fun d => Finset.Ico 1 d)
            (fun d l => (d : K) * (d : K) ^ 2 * ((d - l : ℕ) : K) * Fz v (l : ℤ))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_nat (M.divisors.sigma fun d => Finset.Ico 1 d)
            (fun q => (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K))
            (fun q => q.2)
            (fun q hq => by
              obtain ⟨h1, h2⟩ := bounds_of_mem_pairIdx_Collapse4 hq
              show q.2 ≤ M
              omega)

  have hC3mx : (∑ d ∈ M.divisors,
        (d : K) * (∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d,
          ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
              fun p => Finset.Ico 1 p.1).filter (fun q => q.2 = k ∧ q.1.2 = j),
            (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.1 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    calc ∑ d ∈ M.divisors,
          (d : K) * (∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d,
            ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))
        = ∑ d ∈ M.divisors, ∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d,
            (d : K) * ((d - l : ℕ) : K) * ((d - l' : ℕ) : K)
              * Fz u (l' : ℤ) * Fz v (l : ℤ) :=
          Finset.sum_congr rfl fun d _ => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun l' _ => by ring
      _ = ∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).sigma
            fun p => Finset.Ico 1 p.1,
              (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.1 - q.2 : ℕ) : K)
                * Fz u (q.2 : ℤ) * Fz v (q.1.2 : ℤ) :=
          sum_nest3_eq_sigma M.divisors (fun d => Finset.Ico 1 d)
            (fun d _ => Finset.Ico 1 d)
            (fun d l l' => (d : K) * ((d - l : ℕ) : K) * ((d - l' : ℕ) : K)
              * Fz u (l' : ℤ) * Fz v (l : ℤ))
      _ = _ :=
          sum_mul_Fz_Fz_eq_sum_lines_nat
            ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.1)
            (fun q => (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.1 - q.2 : ℕ) : K))
            (fun q => q.2) (fun q => q.1.2)
            (fun q hq => by
              obtain ⟨h1, h2, h3⟩ := bounds_of_mem_diagIdx_Collapse4 hq
              show q.2 ≤ M
              omega)
            (fun q hq => by
              obtain ⟨h1, h2, h3⟩ := bounds_of_mem_diagIdx_Collapse4 hq
              show q.1.2 ≤ M
              omega)

  have hsplit1 : (∑ d ∈ M.divisors, (d : K) *
        ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) *
          ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ)))))
      = (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
            (d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2 * Fz v (d : ℤ))
        + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
            2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2))
        + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
            (d : K) * ((d - k : ℕ) : K)
              * (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ)) * Fz v (d : ℤ))
        + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
            2 * ((d : K) * ((d - k : ℕ) : K)
              * (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ)))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring

  have hsplit2 : (∑ d ∈ M.divisors, (d : K) *
        ((Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) *
          ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ)))))
      = (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
            (d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2 * Fz u (d : ℤ))
        + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
            2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2))
        + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
            (d : K) * ((d - k : ℕ) : K)
              * (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ)) * Fz u (d : ℤ))
        + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
            2 * ((d : K) * ((d - k : ℕ) : K)
              * (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ)))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring

  have hsplit3 : (∑ d ∈ M.divisors, (d : K) *
        ((d : K) ^ 2 * (d : K) ^ 2
          + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ))
          + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ))
          + ∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d,
              ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ)))
      = (∑ d ∈ M.divisors, (d : K) * ((d : K) ^ 2 * (d : K) ^ 2))
        + (∑ d ∈ M.divisors,
            (d : K) * ((d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ))))
        + (∑ d ∈ M.divisors,
            (d : K) * ((d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ))))
        + (∑ d ∈ M.divisors,
            (d : K) * (∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d,
              ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  calc ∑ d ∈ M.divisors, (d : K) *
        ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) *
            ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ)))
          + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) *
              ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ)))
          - 2 * ((d : K) ^ 2 * (d : K) ^ 2
              + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ))
              + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ))
              + ∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d,
                  ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ)))
      = (∑ d ∈ M.divisors, (d : K) *
            ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) *
              ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ)))))
        + (∑ d ∈ M.divisors, (d : K) *
            ((Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) *
              ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ)))))
        - 2 * (∑ d ∈ M.divisors, (d : K) *
            ((d : K) ^ 2 * (d : K) ^ 2
              + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ))
              + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ))
              + ∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d,
                  ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun d _ => by ring
    _ = _ := by
        rw [hsplit1, hsplit2, hsplit3, hC1pv, hC1mx, hC1pu, hC2pu, hC2mx, hC2pv, hC3pu,
          hC3pv, hC3mx]

end GroupC

section GroupDxCoeff

private theorem bounds_of_mem_xColIdx_Collapse4 {M : ℕ} {q : Σ _ : (Σ _ : ℕ, ℕ), ℕ}
    (hq : q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
      fun p => (M - p.1).divisors) :
    1 ≤ q.1.1 ∧ q.1.1 < M ∧ q.1.2 ≤ q.1.1 ∧ q.2 ≤ M - q.1.1 := by
  have h1 := Finset.mem_sigma.mp hq
  have h2 := Finset.mem_sigma.mp h1.1
  have h3 := Finset.mem_Ico.mp h2.1
  have h4 : q.1.2 ∣ q.1.1 := (Nat.mem_divisors.mp h2.2).1
  have h5 : q.2 ∣ M - q.1.1 := (Nat.mem_divisors.mp h1.2).1
  have h6 : M - q.1.1 ≠ 0 := (Nat.mem_divisors.mp h1.2).2
  exact ⟨h3.1, h3.2, Nat.le_of_dvd (by omega) h4, Nat.le_of_dvd (by omega) h5⟩

private theorem bounds_of_mem_xColIdx4_Collapse4 {M : ℕ}
    {r : Σ _ : (Σ _ : (Σ _ : ℕ, ℕ), ℕ), ℕ}
    (hr : r ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
      fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2) :
    1 ≤ r.1.1.1 ∧ r.1.1.1 < M ∧ r.1.1.2 ≤ r.1.1.1 ∧ r.1.2 ≤ M - r.1.1.1
      ∧ r.2 < r.1.1.2 := by
  have h1 := Finset.mem_sigma.mp hr
  have h2 := bounds_of_mem_xColIdx_Collapse4 h1.1
  have h3 := Finset.mem_Ico.mp h1.2
  exact ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, h3.2⟩

set_option maxHeartbeats 12800000 in

theorem groupD_xCoeff_eq_sum_lines [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (v : K) (M : ℕ) :
    ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ d' ∈ (M - a).divisors,
        (d : K) * (d' : K)
          * ((Fz v ((d : ℤ) + (d' : ℤ)) + Fz v ((d : ℤ) - (d' : ℤ)) - 2 * Fz v (d : ℤ))
              * tent u d)
      = ((∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                  fun p => (M - p.1).divisors).filter
                    (fun q => ((q.1.2 : ℤ) + (q.2 : ℤ)).natAbs = j),
                (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)
                * Fz v (j : ℤ))
          + (∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                  fun p => (M - p.1).divisors).filter
                    (fun q => ((q.1.2 : ℤ) - (q.2 : ℤ)).natAbs = j),
                (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)
                * Fz v (j : ℤ))
          - (∑ j ∈ Finset.Icc 1 M,
              (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                  fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j),
                2 * ((q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2))
                * Fz v (j : ℤ)))
        + ((∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
              (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                  fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
                    (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) + (r.1.2 : ℤ)).natAbs = j),
                (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
                * Fz u (k : ℤ) * Fz v (j : ℤ))
          + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
              (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                  fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
                    (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) - (r.1.2 : ℤ)).natAbs = j),
                (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
                * Fz u (k : ℤ) * Fz v (j : ℤ))
          - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
              (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                  fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
                    (fun r => r.2 = k ∧ r.1.1.2 = j),
                2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K)))
                * Fz u (k : ℤ) * Fz v (j : ℤ))) := by

  have hPVa : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2 * Fz v ((q.1.2 : ℤ) + (q.2 : ℤ)))
      = ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter
                (fun q => ((q.1.2 : ℤ) + (q.2 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)
            * Fz v (j : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
      (fun q => (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)
      (fun q => (q.1.2 : ℤ) + (q.2 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_xColIdx_Collapse4 hq
        show ((q.1.2 : ℤ) + (q.2 : ℤ)).natAbs ≤ M
        omega)

  have hPVb : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2 * Fz v ((q.1.2 : ℤ) - (q.2 : ℤ)))
      = ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter
                (fun q => ((q.1.2 : ℤ) - (q.2 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)
            * Fz v (j : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
      (fun q => (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)
      (fun q => (q.1.2 : ℤ) - (q.2 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_xColIdx_Collapse4 hq
        show ((q.1.2 : ℤ) - (q.2 : ℤ)).natAbs ≤ M
        omega)

  have hPVc : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          2 * ((q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2) * Fz v (q.1.2 : ℤ))
      = ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j),
            2 * ((q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2))
            * Fz v (j : ℤ) :=
    sum_mul_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
      (fun q => 2 * ((q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2))
      (fun q => q.1.2)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_xColIdx_Collapse4 hq
        show q.1.2 ≤ M
        omega)

  have hMXa : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          (q.1.2 : K) * (q.2 : K)
            * (∑ m ∈ Finset.Ico 1 q.1.2, ((q.1.2 - m : ℕ) : K) * Fz u (m : ℤ))
            * Fz v ((q.1.2 : ℤ) + (q.2 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
                (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) + (r.1.2 : ℤ)).natAbs = j),
            (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    calc ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
          fun p => (M - p.1).divisors,
            (q.1.2 : K) * (q.2 : K)
              * (∑ m ∈ Finset.Ico 1 q.1.2, ((q.1.2 - m : ℕ) : K) * Fz u (m : ℤ))
              * Fz v ((q.1.2 : ℤ) + (q.2 : ℤ))
        = ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors, ∑ m ∈ Finset.Ico 1 q.1.2,
              (q.1.2 : K) * (q.2 : K) * ((q.1.2 - m : ℕ) : K)
                * Fz u (m : ℤ) * Fz v ((q.1.2 : ℤ) + (q.2 : ℤ)) :=
          Finset.sum_congr rfl fun q _ => by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun m _ => by ring
      _ = ∑ r ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2,
              (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K)
                * Fz u (r.2 : ℤ) * Fz v ((r.1.1.2 : ℤ) + (r.1.2 : ℤ)) :=
          Finset.sum_sigma'
            (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
            (fun q => Finset.Ico 1 q.1.2)
            (fun q m => (q.1.2 : K) * (q.2 : K) * ((q.1.2 - m : ℕ) : K)
              * Fz u (m : ℤ) * Fz v ((q.1.2 : ℤ) + (q.2 : ℤ)))
      _ = _ :=
          sum_mul_Fz_Fz_eq_sum_lines_nat_int
            ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2)
            (fun r => (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
            (fun r => r.2) (fun r => (r.1.1.2 : ℤ) + (r.1.2 : ℤ))
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_xColIdx4_Collapse4 hr
              show r.2 ≤ M
              omega)
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_xColIdx4_Collapse4 hr
              show ((r.1.1.2 : ℤ) + (r.1.2 : ℤ)).natAbs ≤ M
              omega)

  have hMXb : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          (q.1.2 : K) * (q.2 : K)
            * (∑ m ∈ Finset.Ico 1 q.1.2, ((q.1.2 - m : ℕ) : K) * Fz u (m : ℤ))
            * Fz v ((q.1.2 : ℤ) - (q.2 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
                (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) - (r.1.2 : ℤ)).natAbs = j),
            (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    calc ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
          fun p => (M - p.1).divisors,
            (q.1.2 : K) * (q.2 : K)
              * (∑ m ∈ Finset.Ico 1 q.1.2, ((q.1.2 - m : ℕ) : K) * Fz u (m : ℤ))
              * Fz v ((q.1.2 : ℤ) - (q.2 : ℤ))
        = ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors, ∑ m ∈ Finset.Ico 1 q.1.2,
              (q.1.2 : K) * (q.2 : K) * ((q.1.2 - m : ℕ) : K)
                * Fz u (m : ℤ) * Fz v ((q.1.2 : ℤ) - (q.2 : ℤ)) :=
          Finset.sum_congr rfl fun q _ => by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun m _ => by ring
      _ = ∑ r ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2,
              (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K)
                * Fz u (r.2 : ℤ) * Fz v ((r.1.1.2 : ℤ) - (r.1.2 : ℤ)) :=
          Finset.sum_sigma'
            (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
            (fun q => Finset.Ico 1 q.1.2)
            (fun q m => (q.1.2 : K) * (q.2 : K) * ((q.1.2 - m : ℕ) : K)
              * Fz u (m : ℤ) * Fz v ((q.1.2 : ℤ) - (q.2 : ℤ)))
      _ = _ :=
          sum_mul_Fz_Fz_eq_sum_lines_nat_int
            ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2)
            (fun r => (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
            (fun r => r.2) (fun r => (r.1.1.2 : ℤ) - (r.1.2 : ℤ))
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_xColIdx4_Collapse4 hr
              show r.2 ≤ M
              omega)
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_xColIdx4_Collapse4 hr
              show ((r.1.1.2 : ℤ) - (r.1.2 : ℤ)).natAbs ≤ M
              omega)

  have hMXc : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          2 * ((q.1.2 : K) * (q.2 : K)
            * (∑ m ∈ Finset.Ico 1 q.1.2, ((q.1.2 - m : ℕ) : K) * Fz u (m : ℤ)))
            * Fz v (q.1.2 : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
                (fun r => r.2 = k ∧ r.1.1.2 = j),
            2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    calc ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
          fun p => (M - p.1).divisors,
            2 * ((q.1.2 : K) * (q.2 : K)
              * (∑ m ∈ Finset.Ico 1 q.1.2, ((q.1.2 - m : ℕ) : K) * Fz u (m : ℤ)))
              * Fz v (q.1.2 : ℤ)
        = ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors, ∑ m ∈ Finset.Ico 1 q.1.2,
              2 * ((q.1.2 : K) * (q.2 : K) * ((q.1.2 - m : ℕ) : K))
                * Fz u (m : ℤ) * Fz v (q.1.2 : ℤ) :=
          Finset.sum_congr rfl fun q _ => by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun m _ => by ring
      _ = ∑ r ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2,
              2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
                * Fz u (r.2 : ℤ) * Fz v (r.1.1.2 : ℤ) :=
          Finset.sum_sigma'
            (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
            (fun q => Finset.Ico 1 q.1.2)
            (fun q m => 2 * ((q.1.2 : K) * (q.2 : K) * ((q.1.2 - m : ℕ) : K))
              * Fz u (m : ℤ) * Fz v (q.1.2 : ℤ))
      _ = _ :=
          sum_mul_Fz_Fz_eq_sum_lines_nat
            ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2)
            (fun r => 2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K)))
            (fun r => r.2) (fun r => r.1.1.2)
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_xColIdx4_Collapse4 hr
              show r.2 ≤ M
              omega)
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_xColIdx4_Collapse4 hr
              show r.1.1.2 ≤ M
              omega)

  have hsplit : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          (q.1.2 : K) * (q.2 : K)
            * ((Fz v ((q.1.2 : ℤ) + (q.2 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2 : ℤ))
                - 2 * Fz v (q.1.2 : ℤ)) * tent u q.1.2))
      = ((∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors,
              (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2 * Fz v ((q.1.2 : ℤ) + (q.2 : ℤ)))
          + (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors,
                (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2 * Fz v ((q.1.2 : ℤ) - (q.2 : ℤ)))
          - (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors,
                2 * ((q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2) * Fz v (q.1.2 : ℤ)))
        + ((∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors,
              (q.1.2 : K) * (q.2 : K)
                * (∑ m ∈ Finset.Ico 1 q.1.2, ((q.1.2 - m : ℕ) : K) * Fz u (m : ℤ))
                * Fz v ((q.1.2 : ℤ) + (q.2 : ℤ)))
          + (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors,
                (q.1.2 : K) * (q.2 : K)
                  * (∑ m ∈ Finset.Ico 1 q.1.2, ((q.1.2 - m : ℕ) : K) * Fz u (m : ℤ))
                  * Fz v ((q.1.2 : ℤ) - (q.2 : ℤ)))
          - (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors,
                2 * ((q.1.2 : K) * (q.2 : K)
                  * (∑ m ∈ Finset.Ico 1 q.1.2, ((q.1.2 - m : ℕ) : K) * Fz u (m : ℤ)))
                  * Fz v (q.1.2 : ℤ))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [tent_eq_sq_add_sum_Ico hu0 hu1]
    ring
  calc ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ d' ∈ (M - a).divisors,
        (d : K) * (d' : K)
          * ((Fz v ((d : ℤ) + (d' : ℤ)) + Fz v ((d : ℤ) - (d' : ℤ)) - 2 * Fz v (d : ℤ))
              * tent u d)
      = ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
          fun p => (M - p.1).divisors,
            (q.1.2 : K) * (q.2 : K)
              * ((Fz v ((q.1.2 : ℤ) + (q.2 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2 : ℤ))
                  - 2 * Fz v (q.1.2 : ℤ)) * tent u q.1.2) :=
        sum_nest3_eq_sigma (Finset.Ico 1 M) (fun a => a.divisors)
          (fun a _ => (M - a).divisors)
          (fun _ d d' => (d : K) * (d' : K)
            * ((Fz v ((d : ℤ) + (d' : ℤ)) + Fz v ((d : ℤ) - (d' : ℤ)) - 2 * Fz v (d : ℤ))
                * tent u d))
    _ = _ := by rw [hsplit, hPVa, hPVb, hPVc, hMXa, hMXb, hMXc]

end GroupDxCoeff

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "cauchyMulInt Fz Fz_mul_Fz tent tent_eq_sq_add_sum_Ico add_le_of_mem_Sols sum_mul_Fz_eq_sum_lines_nat sum_mul_Fz_eq_sum_lines_int xCoeffFull a₄Coeff a₆Coeff term b curve xDivTerm xCoeff addDefectSumCoeff cauchyMulIntTriple ks17_C2_exports ks17_C3_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section Bounds

private theorem le_of_mem_divisors_Collapse5 {d M : ℕ} (h : d ∈ M.divisors) : d ≤ M := by
  obtain ⟨h1, h2⟩ := Nat.mem_divisors.mp h
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1

private theorem bounds_of_mem_tentIdx_Collapse5 {M : ℕ} {q : Σ _ : (Σ _ : ℕ, ℕ), ℕ}
    (hq : q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
      fun p => (M - p.1).divisors) :
    1 ≤ q.1.1 ∧ q.1.1 < M ∧ q.1.2 ≤ q.1.1 ∧ q.2 ≤ M - q.1.1 := by
  have h1 := Finset.mem_sigma.mp hq
  have h2 := Finset.mem_sigma.mp h1.1
  have h3 := Finset.mem_Ico.mp h2.1
  have h4 : q.1.2 ∣ q.1.1 := (Nat.mem_divisors.mp h2.2).1
  have h5 : q.2 ∣ M - q.1.1 := (Nat.mem_divisors.mp h1.2).1
  have h6 : M - q.1.1 ≠ 0 := (Nat.mem_divisors.mp h1.2).2
  exact ⟨h3.1, h3.2, Nat.le_of_dvd (by omega) h4, Nat.le_of_dvd (by omega) h5⟩

private theorem bounds_of_mem_tentIdx4_Collapse5 {M : ℕ}
    {r : Σ _ : (Σ _ : (Σ _ : ℕ, ℕ), ℕ), ℕ}
    (hr : r ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
      fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2) :
    1 ≤ r.1.1.1 ∧ r.1.1.1 < M ∧ r.1.1.2 ≤ r.1.1.1 ∧ r.1.2 ≤ M - r.1.1.1
      ∧ r.2 < r.1.2 := by
  have h1 := Finset.mem_sigma.mp hr
  have h2 := bounds_of_mem_tentIdx_Collapse5 h1.1
  have h3 := Finset.mem_Ico.mp h1.2
  exact ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, h3.2⟩

end Bounds

section GroupDTent

set_option maxHeartbeats 12800000 in

theorem groupD_tent_eq_sum_lines (u v : K) (M : ℕ) :
    ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ e ∈ (M - a).divisors,
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
                * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz u (l : ℤ)))
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k ∧ q.1.2 = j),
              (q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2)
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                  (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j),
              (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                  (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j),
              (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                  (fun r => r.1.1.2 = k ∧ r.1.1.2 = j),
              2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k),
              2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2))
              * Fz u (k : ℤ))
        + (∑ k ∈ Finset.Icc 1 M,
            (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                  (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k),
              2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
              * Fz u (k : ℤ))
        + (∑ k ∈ Finset.Icc 1 M,
            (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                  (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k),
              2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
              * Fz u (k : ℤ))
        - (∑ k ∈ Finset.Icc 1 M,
            (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                  (fun r => r.1.1.2 = k),
              4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
              * Fz u (k : ℤ))
        - (∑ k ∈ Finset.Icc 1 M,
            (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                  (fun r => r.2 = k),
              4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
              * Fz u (k : ℤ))
        + (∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
                fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j),
              2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2))
              * Fz v (j : ℤ)) := by

  have hM1 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          (q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2 * Fz u (q.1.2 : ℤ) * Fz v (q.1.2 : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k ∧ q.1.2 = j),
            (q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2)
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
      (fun q => (q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2)
      (fun q => q.1.2) (fun q => q.1.2)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tentIdx_Collapse5 hq
        show q.1.2 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tentIdx_Collapse5 hq
        show q.1.2 ≤ M
        omega)

  have hM2 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          (q.1.2 : K) * (q.2 : K)
            * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u ((q.1.2 : ℤ) + (l : ℤ)))
            * Fz v (q.1.2 : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j),
            (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    calc ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
          fun p => (M - p.1).divisors,
            (q.1.2 : K) * (q.2 : K)
              * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u ((q.1.2 : ℤ) + (l : ℤ)))
              * Fz v (q.1.2 : ℤ)
        = ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors, ∑ l ∈ Finset.Ico 1 q.2,
              (q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K)
                * Fz u ((q.1.2 : ℤ) + (l : ℤ)) * Fz v (q.1.2 : ℤ) :=
          Finset.sum_congr rfl fun q _ => by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ r ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2,
              (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)
                * Fz u ((r.1.1.2 : ℤ) + (r.2 : ℤ)) * Fz v (r.1.1.2 : ℤ) :=
          Finset.sum_sigma'
            (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
            (fun q => Finset.Ico 1 q.2)
            (fun q l => (q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K)
              * Fz u ((q.1.2 : ℤ) + (l : ℤ)) * Fz v (q.1.2 : ℤ))
      _ = _ :=
          sum_mul_Fz_Fz_eq_sum_lines_int_nat
            ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2)
            (fun r => (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
            (fun r => (r.1.1.2 : ℤ) + (r.2 : ℤ)) (fun r => r.1.1.2)
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_tentIdx4_Collapse5 hr
              show ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs ≤ M
              omega)
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_tentIdx4_Collapse5 hr
              show r.1.1.2 ≤ M
              omega)

  have hM3 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          (q.1.2 : K) * (q.2 : K)
            * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u ((q.1.2 : ℤ) - (l : ℤ)))
            * Fz v (q.1.2 : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j),
            (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    calc ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
          fun p => (M - p.1).divisors,
            (q.1.2 : K) * (q.2 : K)
              * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u ((q.1.2 : ℤ) - (l : ℤ)))
              * Fz v (q.1.2 : ℤ)
        = ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors, ∑ l ∈ Finset.Ico 1 q.2,
              (q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K)
                * Fz u ((q.1.2 : ℤ) - (l : ℤ)) * Fz v (q.1.2 : ℤ) :=
          Finset.sum_congr rfl fun q _ => by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ r ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2,
              (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)
                * Fz u ((r.1.1.2 : ℤ) - (r.2 : ℤ)) * Fz v (r.1.1.2 : ℤ) :=
          Finset.sum_sigma'
            (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
            (fun q => Finset.Ico 1 q.2)
            (fun q l => (q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K)
              * Fz u ((q.1.2 : ℤ) - (l : ℤ)) * Fz v (q.1.2 : ℤ))
      _ = _ :=
          sum_mul_Fz_Fz_eq_sum_lines_int_nat
            ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2)
            (fun r => (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
            (fun r => (r.1.1.2 : ℤ) - (r.2 : ℤ)) (fun r => r.1.1.2)
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_tentIdx4_Collapse5 hr
              show ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs ≤ M
              omega)
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_tentIdx4_Collapse5 hr
              show r.1.1.2 ≤ M
              omega)

  have hM4 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          2 * ((q.1.2 : K) * (q.2 : K)
            * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (q.1.2 : ℤ)))
            * Fz v (q.1.2 : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => r.1.1.2 = k ∧ r.1.1.2 = j),
            2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    calc ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
          fun p => (M - p.1).divisors,
            2 * ((q.1.2 : K) * (q.2 : K)
              * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (q.1.2 : ℤ)))
              * Fz v (q.1.2 : ℤ)
        = ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors, ∑ l ∈ Finset.Ico 1 q.2,
              2 * ((q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K))
                * Fz u (q.1.2 : ℤ) * Fz v (q.1.2 : ℤ) :=
          Finset.sum_congr rfl fun q _ => by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ r ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2,
              2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
                * Fz u (r.1.1.2 : ℤ) * Fz v (r.1.1.2 : ℤ) :=
          Finset.sum_sigma'
            (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
            (fun q => Finset.Ico 1 q.2)
            (fun q l => 2 * ((q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K))
              * Fz u (q.1.2 : ℤ) * Fz v (q.1.2 : ℤ))
      _ = _ :=
          sum_mul_Fz_Fz_eq_sum_lines_nat
            ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2)
            (fun r => 2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            (fun r => r.1.1.2) (fun r => r.1.1.2)
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_tentIdx4_Collapse5 hr
              show r.1.1.2 ≤ M
              omega)
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_tentIdx4_Collapse5 hr
              show r.1.1.2 ≤ M
              omega)

  have hU1 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2) * Fz u (q.1.2 : ℤ))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k),
            2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
      (fun q => 2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2))
      (fun q => q.1.2)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tentIdx_Collapse5 hq
        show q.1.2 ≤ M
        omega)

  have hU2 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          2 * ((q.1.2 : K) * (q.2 : K)
            * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u ((q.1.2 : ℤ) + (l : ℤ)))))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k),
            2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ) :=
    calc ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
          fun p => (M - p.1).divisors,
            2 * ((q.1.2 : K) * (q.2 : K)
              * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u ((q.1.2 : ℤ) + (l : ℤ))))
        = ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors, ∑ l ∈ Finset.Ico 1 q.2,
              2 * ((q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K))
                * Fz u ((q.1.2 : ℤ) + (l : ℤ)) :=
          Finset.sum_congr rfl fun q _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ r ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2,
              2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
                * Fz u ((r.1.1.2 : ℤ) + (r.2 : ℤ)) :=
          Finset.sum_sigma'
            (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
            (fun q => Finset.Ico 1 q.2)
            (fun q l => 2 * ((q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K))
              * Fz u ((q.1.2 : ℤ) + (l : ℤ)))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_int
            ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2)
            (fun r => 2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            (fun r => (r.1.1.2 : ℤ) + (r.2 : ℤ))
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_tentIdx4_Collapse5 hr
              show ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs ≤ M
              omega)

  have hU3 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          2 * ((q.1.2 : K) * (q.2 : K)
            * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u ((q.1.2 : ℤ) - (l : ℤ)))))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k),
            2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ) :=
    calc ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
          fun p => (M - p.1).divisors,
            2 * ((q.1.2 : K) * (q.2 : K)
              * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u ((q.1.2 : ℤ) - (l : ℤ))))
        = ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors, ∑ l ∈ Finset.Ico 1 q.2,
              2 * ((q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K))
                * Fz u ((q.1.2 : ℤ) - (l : ℤ)) :=
          Finset.sum_congr rfl fun q _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ r ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2,
              2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
                * Fz u ((r.1.1.2 : ℤ) - (r.2 : ℤ)) :=
          Finset.sum_sigma'
            (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
            (fun q => Finset.Ico 1 q.2)
            (fun q l => 2 * ((q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K))
              * Fz u ((q.1.2 : ℤ) - (l : ℤ)))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_int
            ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2)
            (fun r => 2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            (fun r => (r.1.1.2 : ℤ) - (r.2 : ℤ))
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_tentIdx4_Collapse5 hr
              show ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs ≤ M
              omega)

  have hU4 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          4 * ((q.1.2 : K) * (q.2 : K)
            * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (q.1.2 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => r.1.1.2 = k),
            4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ) :=
    calc ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
          fun p => (M - p.1).divisors,
            4 * ((q.1.2 : K) * (q.2 : K)
              * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (q.1.2 : ℤ)))
        = ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors, ∑ l ∈ Finset.Ico 1 q.2,
              4 * ((q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K))
                * Fz u (q.1.2 : ℤ) :=
          Finset.sum_congr rfl fun q _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ r ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2,
              4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
                * Fz u (r.1.1.2 : ℤ) :=
          Finset.sum_sigma'
            (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
            (fun q => Finset.Ico 1 q.2)
            (fun q l => 4 * ((q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K))
              * Fz u (q.1.2 : ℤ))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_nat
            ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2)
            (fun r => 4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            (fun r => r.1.1.2)
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_tentIdx4_Collapse5 hr
              show r.1.1.2 ≤ M
              omega)

  have hU5 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          4 * ((q.1.2 : K) * (q.2 : K)
            * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (l : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => r.2 = k),
            4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ) :=
    calc ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
          fun p => (M - p.1).divisors,
            4 * ((q.1.2 : K) * (q.2 : K)
              * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (l : ℤ)))
        = ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors, ∑ l ∈ Finset.Ico 1 q.2,
              4 * ((q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K))
                * Fz u (l : ℤ) :=
          Finset.sum_congr rfl fun q _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ r ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2,
              4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
                * Fz u (r.2 : ℤ) :=
          Finset.sum_sigma'
            (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
            (fun q => Finset.Ico 1 q.2)
            (fun q l => 4 * ((q.1.2 : K) * (q.2 : K) * ((q.2 - l : ℕ) : K))
              * Fz u (l : ℤ))
      _ = _ :=
          sum_mul_Fz_eq_sum_lines_nat
            ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2)
            (fun r => 4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            (fun r => r.2)
            (fun r hr => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := bounds_of_mem_tentIdx4_Collapse5 hr
              show r.2 ≤ M
              omega)

  have hV1 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2) * Fz v (q.1.2 : ℤ))
      = ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j),
            2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2))
            * Fz v (j : ℤ) :=
    sum_mul_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors)
      (fun q => 2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2))
      (fun q => q.1.2)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_tentIdx_Collapse5 hq
        show q.1.2 ≤ M
        omega)

  have hsplit : (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
        fun p => (M - p.1).divisors,
          (q.1.2 : K) * (q.2 : K)
            * (Fz v (q.1.2 : ℤ) * ((q.2 : K) ^ 2 * Fz u (q.1.2 : ℤ)
                  + ∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K)
                      * (Fz u ((q.1.2 : ℤ) + (l : ℤ)) + Fz u ((q.1.2 : ℤ) - (l : ℤ))
                          - 2 * Fz u (q.1.2 : ℤ) - 2 * Fz u (l : ℤ)))
              + 2 * ((q.2 : K) ^ 2 * Fz u (q.1.2 : ℤ)
                  + ∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K)
                      * (Fz u ((q.1.2 : ℤ) + (l : ℤ)) + Fz u ((q.1.2 : ℤ) - (l : ℤ))
                          - 2 * Fz u (q.1.2 : ℤ) - 2 * Fz u (l : ℤ)))
              + 2 * Fz v (q.1.2 : ℤ)
                  * ((q.2 : K) ^ 2
                      + ∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (l : ℤ))))
      = (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors,
              (q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2 * Fz u (q.1.2 : ℤ) * Fz v (q.1.2 : ℤ))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors,
              (q.1.2 : K) * (q.2 : K)
                * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K)
                    * Fz u ((q.1.2 : ℤ) + (l : ℤ)))
                * Fz v (q.1.2 : ℤ))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors,
              (q.1.2 : K) * (q.2 : K)
                * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K)
                    * Fz u ((q.1.2 : ℤ) - (l : ℤ)))
                * Fz v (q.1.2 : ℤ))
        - (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors,
              2 * ((q.1.2 : K) * (q.2 : K)
                * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (q.1.2 : ℤ)))
                * Fz v (q.1.2 : ℤ))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors,
              2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2) * Fz u (q.1.2 : ℤ))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors,
              2 * ((q.1.2 : K) * (q.2 : K)
                * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K)
                    * Fz u ((q.1.2 : ℤ) + (l : ℤ)))))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors,
              2 * ((q.1.2 : K) * (q.2 : K)
                * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K)
                    * Fz u ((q.1.2 : ℤ) - (l : ℤ)))))
        - (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors,
              4 * ((q.1.2 : K) * (q.2 : K)
                * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (q.1.2 : ℤ))))
        - (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors,
              4 * ((q.1.2 : K) * (q.2 : K)
                * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (l : ℤ))))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors,
              2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2) * Fz v (q.1.2 : ℤ)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hb : (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K)
          * (Fz u ((q.1.2 : ℤ) + (l : ℤ)) + Fz u ((q.1.2 : ℤ) - (l : ℤ))
              - 2 * Fz u (q.1.2 : ℤ) - 2 * Fz u (l : ℤ)))
        = (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u ((q.1.2 : ℤ) + (l : ℤ)))
          + (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u ((q.1.2 : ℤ) - (l : ℤ)))
          - 2 * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (q.1.2 : ℤ))
          - 2 * (∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (l : ℤ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hb]
    ring
  calc ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ e ∈ (M - a).divisors,
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
                * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz u (l : ℤ)))
      = ∑ q ∈ ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
          fun p => (M - p.1).divisors,
            (q.1.2 : K) * (q.2 : K)
              * (Fz v (q.1.2 : ℤ) * ((q.2 : K) ^ 2 * Fz u (q.1.2 : ℤ)
                    + ∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K)
                        * (Fz u ((q.1.2 : ℤ) + (l : ℤ)) + Fz u ((q.1.2 : ℤ) - (l : ℤ))
                            - 2 * Fz u (q.1.2 : ℤ) - 2 * Fz u (l : ℤ)))
                + 2 * ((q.2 : K) ^ 2 * Fz u (q.1.2 : ℤ)
                    + ∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K)
                        * (Fz u ((q.1.2 : ℤ) + (l : ℤ)) + Fz u ((q.1.2 : ℤ) - (l : ℤ))
                            - 2 * Fz u (q.1.2 : ℤ) - 2 * Fz u (l : ℤ)))
                + 2 * Fz v (q.1.2 : ℤ)
                    * ((q.2 : K) ^ 2
                        + ∑ l ∈ Finset.Ico 1 q.2, ((q.2 - l : ℕ) : K) * Fz u (l : ℤ))) :=
        sum_nest3_eq_sigma (Finset.Ico 1 M) (fun a => a.divisors)
          (fun a _ => (M - a).divisors)
          (fun _ d e => (d : K) * (e : K)
            * (Fz v (d : ℤ) * ((e : K) ^ 2 * Fz u (d : ℤ)
                  + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K)
                      * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ))
                          - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ)))
              + 2 * ((e : K) ^ 2 * Fz u (d : ℤ)
                  + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K)
                      * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ))
                          - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ)))
              + 2 * Fz v (d : ℤ)
                  * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz u (l : ℤ))))
    _ = _ := by rw [hsplit, hM1, hM2, hM3, hM4, hU1, hU2, hU3, hU4, hU5, hV1]

end GroupDTent

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "cauchyMulInt Fz Fz_mul_Fz tent tent_eq_sq_add_sum_Ico add_le_of_mem_Sols sum_mul_Fz_eq_sum_lines_nat sum_mul_Fz_eq_sum_lines_int xCoeffFull a₄Coeff a₆Coeff term b curve xDivTerm xCoeff addDefectSumCoeff cauchyMulIntTriple ks17_C2_exports ks17_C3_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section PerIndex

theorem Fz_mul_Fz_mul_Fz (hu0 : u ≠ 0) (a b c : ℤ) :
    Fz u a * Fz u b * Fz u c
      = Fz u (a + (b + c)) + Fz u (a + (b - c)) + Fz u (a - (b - c)) + Fz u (a - (b + c))
        - 2 * (Fz u (a + b) + Fz u (a - b)) - 2 * (Fz u (a + c) + Fz u (a - c))
        + 4 * Fz u a
        - 2 * (Fz u (b + c) + Fz u (b - c)) + 4 * Fz u b + 4 * Fz u c := by
  linear_combination (Fz u a) * Fz_mul_Fz hu0 b c + Fz_mul_Fz hu0 a (b + c)
    + Fz_mul_Fz hu0 a (b - c) - 2 * Fz_mul_Fz hu0 a b - 2 * Fz_mul_Fz hu0 a c

theorem crossFactor_mul_diff_mul_diff (hu0 : u ≠ 0) (hv0 : v ≠ 0) (d b c : ℤ) :
    (Fz u d * Fz v d + 2 * Fz u d + 2 * Fz v d)
        * ((Fz u b - Fz v b) * (Fz u c - Fz v c))
      = (Fz u (d + (b + c)) + Fz u (d + (b - c)) + Fz u (d - (b - c)) + Fz u (d - (b + c)))
            * Fz v d
        + Fz u d * (Fz v (d + (b + c)) + Fz v (d + (b - c)) + Fz v (d - (b - c))
            + Fz v (d - (b + c)))
        + 4 * (Fz u b * Fz v c) + 4 * (Fz u c * Fz v b)
        - (Fz u (d + b) + Fz u (d - b)) * (Fz v (d + c) + Fz v (d - c))
        - (Fz u (d + c) + Fz u (d - c)) * (Fz v (d + b) + Fz v (d - b))
        + 2 * (Fz u d * Fz u b * Fz u c) + 2 * (Fz v d * Fz v b * Fz v c) := by
  linear_combination
    (Fz u d * Fz v d + 2 * Fz u d + 2 * Fz v d) * Fz_mul_Fz hu0 b c
      + (Fz u d * Fz v d + 2 * Fz u d + 2 * Fz v d) * Fz_mul_Fz hv0 b c
      + crossFactor_mul_Fz_left (v := v) hu0 d (b + c)
      + crossFactor_mul_Fz_left (v := v) hu0 d (b - c)
      - 2 * crossFactor_mul_Fz_left (v := v) hu0 d b
      - 2 * crossFactor_mul_Fz_left (v := v) hu0 d c
      + crossFactor_mul_Fz_right (u := u) hv0 d (b + c)
      + crossFactor_mul_Fz_right (u := u) hv0 d (b - c)
      - 2 * crossFactor_mul_Fz_right (u := u) hv0 d b
      - 2 * crossFactor_mul_Fz_right (u := u) hv0 d c
      - Fz_mul_Fz_mul_Fz_mul_Fz hu0 hv0 d d b c
      - 2 * Fz v c * Fz_mul_Fz hu0 d b - 2 * Fz u b * Fz_mul_Fz hv0 d c
      - Fz_mul_Fz_mul_Fz_mul_Fz hu0 hv0 d d c b
      - 2 * Fz v b * Fz_mul_Fz hu0 d c - 2 * Fz u c * Fz_mul_Fz hv0 d b
      - 2 * Fz_mul_Fz_mul_Fz hu0 d b c - 2 * Fz_mul_Fz_mul_Fz hv0 d b c

end PerIndex

section Bounds

private theorem bounds_of_mem_diffsqIdx_Collapse6 {M : ℕ}
    {q : Σ _ : (Σ _ : ℕ, ℕ), ℕ × ℕ × ℕ × ℕ}
    (hq : q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)) :
    1 ≤ q.1.1 ∧ q.1.1 < M ∧ q.1.2 ≤ q.1.1 ∧ q.2.1 + q.2.2.2.1 ≤ M - q.1.1 := by
  have h1 := Finset.mem_sigma.mp hq
  have h2 := Finset.mem_sigma.mp h1.1
  have h3 := Finset.mem_Ico.mp h2.1
  have h4 : q.1.2 ∣ q.1.1 := (Nat.mem_divisors.mp h2.2).1
  have h5 := add_le_of_mem_Sols h1.2
  exact ⟨h3.1, h3.2, Nat.le_of_dvd (by omega) h4, h5⟩

end Bounds

section PureCollapse

set_option maxHeartbeats 6400000 in

theorem groupD_diffsq_pure_eq_sum_lines (hu0 : u ≠ 0) (M : ℕ) :
    ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1),
        (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
          * (Fz u (q.1.2 : ℤ) * Fz u (q.2.1 : ℤ) * Fz u (q.2.2.2.1 : ℤ))
      = (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ))
        + (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ))
        + (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ))
        + (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ))
        - 2 * (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ))
        - 2 * (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ))
        - 2 * (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ))
        - 2 * (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ))
        + 4 * (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.1.2 = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ))
        - 2 * (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.2.1 + q.2.2.2.1 = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ))
        - 2 * (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ))
        + 4 * (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.2.1 = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ))
        + 4 * (∑ k ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.2.2.2.1 = k),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ)) := by

  have hc1 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs ≤ M
        omega)
  have hc2 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs ≤ M
        omega)
  have hc3 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs ≤ M
        omega)
  have hc4 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs ≤ M
        omega)
  have hc5 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + (q.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hc6 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) - (q.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hc7 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + (q.2.2.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hc8 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) - (q.2.2.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hc9 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℕ) : ℤ))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.1.2)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.1.2 ≤ M
        omega)
  have hc10 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.2.1 + q.2.2.2.1 : ℕ) : ℤ))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.2.1 + q.2.2.2.1 = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.2.1 + q.2.2.2.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.2.1 + q.2.2.2.1 ≤ M
        omega)
  have hc11 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hc12 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.2.1 : ℕ) : ℤ))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.2.1 = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.2.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.2.1 ≤ M
        omega)
  have hc13 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.2.2.2.1 : ℕ) : ℤ))
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.2.2.2.1 = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.2.2.2.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.2.2.2.1 ≤ M
        omega)

  have hsplit : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * (Fz u (q.1.2 : ℤ) * Fz u (q.2.1 : ℤ) * Fz u (q.2.2.2.1 : ℤ)))
      = (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))))
        - 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)))
        - 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ)))
        - 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)))
        - 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
        + 4 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℕ) : ℤ))
        - 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.2.1 + q.2.2.2.1 : ℕ) : ℤ))
        - 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
        + 4 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.2.1 : ℕ) : ℤ))
        + 4 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.2.2.2.1 : ℕ) : ℤ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have h := Fz_mul_Fz_mul_Fz hu0 (q.1.2 : ℤ) (q.2.1 : ℤ) (q.2.2.2.1 : ℤ)
    push_cast
    linear_combination ((q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * h
  rw [hsplit, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

end PureCollapse

section MixedCollapse

set_option maxHeartbeats 12800000 in

theorem groupD_diffsq_mixed_eq_sum_lines (u v : K) (M : ℕ) :
    ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1),
        (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
          * ((Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
                + Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))) * Fz v (q.1.2 : ℤ)
            + Fz u (q.1.2 : ℤ)
                * (Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
                  + Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                  + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                  + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))))
            + 4 * (Fz u (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ))
            + 4 * (Fz u (q.2.2.2.1 : ℤ) * Fz v (q.2.1 : ℤ))
            - (Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ)))
                * (Fz v ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
            - (Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
                * (Fz v ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.1 : ℤ))))
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k
                    ∧ q.1.2 = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k
                    ∧ q.1.2 = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k
                    ∧ q.1.2 = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k
                    ∧ q.1.2 = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.1.2 = k
                    ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.1.2 = k
                    ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.1.2 = k
                    ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.1.2 = k
                    ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + 4 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.2.1 = k ∧ q.2.2.2.1 = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        + 4 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => q.2.2.2.1 = k ∧ q.2.1 = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k
                    ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k
                    ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k
                    ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k
                    ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k
                    ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k
                    ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k
                    ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ))
        - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
                fun p => Sols (M - p.1)).filter
                  (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k
                    ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
              * Fz u (k : ℤ) * Fz v (j : ℤ)) := by

  have hb1 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))) * Fz v ((q.1.2 : ℕ) : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k
                  ∧ q.1.2 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))) (fun q => q.1.2)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.1.2 ≤ M
        omega)
  have hb2 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) * Fz v ((q.1.2 : ℕ) : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k
                  ∧ q.1.2 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) (fun q => q.1.2)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.1.2 ≤ M
        omega)
  have hb3 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) * Fz v ((q.1.2 : ℕ) : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k
                  ∧ q.1.2 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) (fun q => q.1.2)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.1.2 ≤ M
        omega)
  have hb4 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))) * Fz v ((q.1.2 : ℕ) : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k
                  ∧ q.1.2 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))) (fun q => q.1.2)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.1.2 ≤ M
        omega)
  have hb5 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℕ) : ℤ) * Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k
                  ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_nat_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.1.2) (fun q => (q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.1.2 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs ≤ M
        omega)
  have hb6 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℕ) : ℤ) * Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k
                  ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_nat_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.1.2) (fun q => (q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.1.2 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs ≤ M
        omega)
  have hb7 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℕ) : ℤ) * Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k
                  ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_nat_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.1.2) (fun q => (q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.1.2 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs ≤ M
        omega)
  have hb8 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℕ) : ℤ) * Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k
                  ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_nat_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.1.2) (fun q => (q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.1.2 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs ≤ M
        omega)
  have hb9 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.2.1 : ℕ) : ℤ) * Fz v ((q.2.2.2.1 : ℕ) : ℤ))
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
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.2.1 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.2.2.2.1 ≤ M
        omega)
  have hb10 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.2.2.2.1 : ℕ) : ℤ) * Fz v ((q.2.1 : ℕ) : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.2.2.2.1 = k ∧ q.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_nat
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => q.2.2.2.1) (fun q => q.2.1)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.2.2.2.1 ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show q.2.1 ≤ M
        omega)
  have hb11 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + (q.2.1 : ℤ)) (fun q => (q.1.2 : ℤ) + (q.2.2.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hb12 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + (q.2.1 : ℤ)) (fun q => (q.1.2 : ℤ) - (q.2.2.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hb13 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) - (q.2.1 : ℤ)) (fun q => (q.1.2 : ℤ) + (q.2.2.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hb14 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) - (q.2.1 : ℤ)) (fun q => (q.1.2 : ℤ) - (q.2.2.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hb15 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) + (q.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) (fun q => (q.1.2 : ℤ) + (q.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hb16 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) - (q.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) (fun q => (q.1.2 : ℤ) - (q.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hb17 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) + (q.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)) (fun q => (q.1.2 : ℤ) + (q.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs ≤ M
        omega)
  have hb18 : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) - (q.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ) :=
    sum_mul_Fz_Fz_eq_sum_lines_int
      (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1))
      (fun q => (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
      (fun q => (q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)) (fun q => (q.1.2 : ℤ) - (q.2.1 : ℤ))
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs ≤ M
        omega)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := bounds_of_mem_diffsqIdx_Collapse6 hq
        show ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs ≤ M
        omega)

  have hsplit : (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
        fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * ((Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
                  + Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                  + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                  + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))) * Fz v (q.1.2 : ℤ)
              + Fz u (q.1.2 : ℤ)
                  * (Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
                    + Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                    + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                    + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))))
              + 4 * (Fz u (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ))
              + 4 * (Fz u (q.2.2.2.1 : ℤ) * Fz v (q.2.1 : ℤ))
              - (Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ)))
                  * (Fz v ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ))
                    + Fz v ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
              - (Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
                  * (Fz v ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.1 : ℤ)))))
      = (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
                * Fz v ((q.1.2 : ℕ) : ℤ))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                * Fz v ((q.1.2 : ℕ) : ℤ))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                * Fz v ((q.1.2 : ℕ) : ℤ))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
                * Fz v ((q.1.2 : ℕ) : ℤ))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℕ) : ℤ)
                * Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℕ) : ℤ)
                * Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℕ) : ℤ)
                * Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))))
        + (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℕ) : ℤ)
                * Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))))
        + 4 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.2.1 : ℕ) : ℤ) * Fz v ((q.2.2.2.1 : ℕ) : ℤ))
        + 4 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.2.2.2.1 : ℕ) : ℤ) * Fz v ((q.2.1 : ℕ) : ℤ))
        - (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)))
        - (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
        - (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)))
        - (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
        - (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) + (q.2.1 : ℤ)))
        - (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) - (q.2.1 : ℤ)))
        - (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) + (q.2.1 : ℤ)))
        - (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)) * Fz v ((q.1.2 : ℤ) - (q.2.1 : ℤ))) := by
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hsplit, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14,
    hb15, hb16, hb17, hb18]

end MixedCollapse

section BlockSplit

set_option maxHeartbeats 3200000 in

theorem groupD_diffsq_eq_sum_lines (hu0 : u ≠ 0) (hv0 : v ≠ 0) (M : ℕ) :
    ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ x ∈ Sols (M - a),
        (d : K) * (x.1 : K) * (x.2.2.1 : K)
          * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ))
          * ((Fz u (x.1 : ℤ) - Fz v (x.1 : ℤ))
              * (Fz u (x.2.2.1 : ℤ) - Fz v (x.2.2.1 : ℤ)))
      = (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
              * ((Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
                    + Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                    + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                    + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))) * Fz v (q.1.2 : ℤ)
                + Fz u (q.1.2 : ℤ)
                    * (Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
                      + Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                      + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                      + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))))
                + 4 * (Fz u (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ))
                + 4 * (Fz u (q.2.2.2.1 : ℤ) * Fz v (q.2.1 : ℤ))
                - (Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ)))
                    * (Fz v ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ))
                      + Fz v ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
                - (Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
                    * (Fz v ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.1 : ℤ)))))
        + 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * (Fz u (q.1.2 : ℤ) * Fz u (q.2.1 : ℤ) * Fz u (q.2.2.2.1 : ℤ)))
        + 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1),
              (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * (Fz v (q.1.2 : ℤ) * Fz v (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ))) := by
  calc ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ x ∈ Sols (M - a),
        (d : K) * (x.1 : K) * (x.2.2.1 : K)
          * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ))
          * ((Fz u (x.1 : ℤ) - Fz v (x.1 : ℤ))
              * (Fz u (x.2.2.1 : ℤ) - Fz v (x.2.2.1 : ℤ)))
      = ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
            * (Fz u (q.1.2 : ℤ) * Fz v (q.1.2 : ℤ) + 2 * Fz u (q.1.2 : ℤ)
                + 2 * Fz v (q.1.2 : ℤ))
            * ((Fz u (q.2.1 : ℤ) - Fz v (q.2.1 : ℤ))
                * (Fz u (q.2.2.2.1 : ℤ) - Fz v (q.2.2.2.1 : ℤ))) :=
        sum_Ico_divisors_Sols_eq_sigma M
          (fun i d x => (d : K) * (x.1 : K) * (x.2.2.1 : K)
            * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ))
            * ((Fz u (x.1 : ℤ) - Fz v (x.1 : ℤ))
                * (Fz u (x.2.2.1 : ℤ) - Fz v (x.2.2.1 : ℤ))))
    _ = ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1),
          ((q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
              * ((Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
                    + Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                    + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                    + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))) * Fz v (q.1.2 : ℤ)
                + Fz u (q.1.2 : ℤ)
                    * (Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))
                      + Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                      + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)))
                      + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))))
                + 4 * (Fz u (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ))
                + 4 * (Fz u (q.2.2.2.1 : ℤ) * Fz v (q.2.1 : ℤ))
                - (Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ)))
                    * (Fz v ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ))
                      + Fz v ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
                - (Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ))
                      + Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)))
                    * (Fz v ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.1 : ℤ))))
            + 2 * ((q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * (Fz u (q.1.2 : ℤ) * Fz u (q.2.1 : ℤ) * Fz u (q.2.2.2.1 : ℤ)))
            + 2 * ((q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)
                * (Fz v (q.1.2 : ℤ) * Fz v (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ)))) :=
        Finset.sum_congr rfl fun q _ => by
          linear_combination ((q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * crossFactor_mul_diff_mul_diff hu0 hv0 (q.1.2 : ℤ) (q.2.1 : ℤ) (q.2.2.2.1 : ℤ)
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end BlockSplit

end TateCurve

theorem solution :
    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      ∑ d ∈ M.divisors, (d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ))) + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ))) - 2 * ((d : K) ^ 2 * (d : K) ^ 2 + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ)) + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) = ((∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.1 = j), (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2) * Fz v (j : ℤ)) + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d, 2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = k ∧ q.1.1 = j), (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = k), 2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))) * Fz u (k : ℤ))) + ((∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.1 = k), (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2) * Fz u (k : ℤ)) + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d, 2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.1.1 = k ∧ q.2 = j), (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j), 2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))) * Fz v (j : ℤ))) - 2 * ((∑ d ∈ M.divisors, (d : K) * ((d : K) ^ 2 * (d : K) ^ 2)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.2 = k), (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K)) * Fz u (k : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.2 = j), (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K)) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.1).filter (fun q => q.2 = k ∧ q.1.2 = j), (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.1 - q.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ e ∈ (M - a).divisors, (d : K) * (e : K) * (Fz v (d : ℤ) * ((e : K) ^ 2 * Fz u (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ))) + 2 * ((e : K) ^ 2 * Fz u (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ))) + 2 * Fz v (d : ℤ) * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz u (l : ℤ))) = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k ∧ q.1.2 = j), (q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j), (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j), (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => r.1.1.2 = k ∧ r.1.1.2 = j), 2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k), 2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2)) * Fz u (k : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k), 2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))) * Fz u (k : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k), 2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))) * Fz u (k : ℤ)) - (∑ k ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => r.1.1.2 = k), 4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))) * Fz u (k : ℤ)) - (∑ k ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => r.2 = k), 4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))) * Fz u (k : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j), 2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2)) * Fz v (j : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (v : K) (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ d' ∈ (M - a).divisors, (d : K) * (d' : K) * ((Fz v ((d : ℤ) + (d' : ℤ)) + Fz v ((d : ℤ) - (d' : ℤ)) - 2 * Fz v (d : ℤ)) * tent u d) = ((∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).filter (fun q => ((q.1.2 : ℤ) + (q.2 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2) * Fz v (j : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).filter (fun q => ((q.1.2 : ℤ) - (q.2 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2) * Fz v (j : ℤ)) - (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j), 2 * ((q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)) * Fz v (j : ℤ))) + ((∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) + (r.1.2 : ℤ)).natAbs = j), (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) - (r.1.2 : ℤ)).natAbs = j), (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter (fun r => r.2 = k ∧ r.1.1.2 = j), 2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))) * Fz u (k : ℤ) * Fz v (j : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ x ∈ Sols (M - a), (d : K) * (x.1 : K) * (x.2.2.1 : K) * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ)) * ((Fz u (x.1 : ℤ) - Fz v (x.1 : ℤ)) * (Fz u (x.2.2.1 : ℤ) - Fz v (x.2.2.1 : ℤ))) = (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K) * ((Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))) + Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))) * Fz v (q.1.2 : ℤ) + Fz u (q.1.2 : ℤ) * (Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))) + Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))) + 4 * (Fz u (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ)) + 4 * (Fz u (q.2.2.2.1 : ℤ) * Fz v (q.2.1 : ℤ)) - (Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ))) * (Fz v ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ))) - (Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ))) * (Fz v ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.1 : ℤ))))) + 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K) * (Fz u (q.1.2 : ℤ) * Fz u (q.2.1 : ℤ) * Fz u (q.2.2.2.1 : ℤ))) + 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K) * (Fz v (q.1.2 : ℤ) * Fz v (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K) * ((Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))) + Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))) * Fz v (q.1.2 : ℤ) + Fz u (q.1.2 : ℤ) * (Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))) + Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))) + 4 * (Fz u (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ)) + 4 * (Fz u (q.2.2.2.1 : ℤ) * Fz v (q.2.1 : ℤ)) - (Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ))) * (Fz v ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ))) - (Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ))) * (Fz v ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.1 : ℤ)))) = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k ∧ q.1.2 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k ∧ q.1.2 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k ∧ q.1.2 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k ∧ q.1.2 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + 4 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + 4 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.2.2.1 = k ∧ q.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (M : ℕ),
      ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K) * (Fz u (q.1.2 : ℤ) * Fz u (q.2.1 : ℤ) * Fz u (q.2.2.2.1 : ℤ)) = (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) + 4 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.1 + q.2.2.2.1 = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) + 4 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) + 4 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.2.2.1 = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ))) :=
  ⟨TateCurve.groupC_eq_sum_lines, TateCurve.groupD_tent_eq_sum_lines, TateCurve.groupD_xCoeff_eq_sum_lines, TateCurve.groupD_diffsq_eq_sum_lines, TateCurve.groupD_diffsq_mixed_eq_sum_lines, TateCurve.groupD_diffsq_pure_eq_sum_lines⟩

end S_TateCurve_ks17_D3_exports
end P2MW
export P2MW.S_TateCurve_ks17_D3_exports (solution)
