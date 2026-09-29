-- Prove2me | solution 1 for TateCurve.ks17_C1_exports
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/2e593801-6d7f-5d54-886d-2afc816b378b

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

namespace P2MW.S_TateCurve_ks17_C1_exports

open scoped NNReal
p2m_open "TateCurve P2MW.S_TateCurve_ks17_C1_exports.TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset"

universe u_1 u_2

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows rows_eval_eq_zero_of_master_at_spectators symSumNum symProdNum AddParams addDefectSum addDefectProd addDefectSum_eq_zero_iff addDefectProd_eq_zero_iff addDefectSum_q_mul_left norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma spec_eq_zero_of_master ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMulInt sum_Ico_divisorSum_mul_eq_sum_Sols Fz Gz Gz_neg Fz_mul_Gz xDivTerm_eq_mul_Fz tent tent_one cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice MuTranslation ks17_A_exports ks17_B_exports"
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

namespace AddParams p2m_export "TateCurve.AddParams" "swap v_ne_zero q_ne_zero mk" end AddParams
p2m_open_scoped "TateCurve.AddParams" in
theorem AddParams.latticeRep : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} {u' v' : K} (hp : AddParams q u v)
    (hu' : LatticeRep q u u') (hv' : LatticeRep q v v'),
      AddParams q u' v' :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end TateCurve

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows rows_eval_eq_zero_of_master_at_spectators symSumNum symProdNum AddParams addDefectSum addDefectProd addDefectSum_eq_zero_iff addDefectProd_eq_zero_iff addDefectSum_q_mul_left norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma spec_eq_zero_of_master ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMulInt sum_Ico_divisorSum_mul_eq_sum_Sols Fz Gz Gz_neg Fz_mul_Gz xDivTerm_eq_mul_Fz tent tent_one cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice MuTranslation ks17_A_exports ks17_B_exports"
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

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows rows_eval_eq_zero_of_master_at_spectators symSumNum symProdNum AddParams addDefectSum addDefectProd addDefectSum_eq_zero_iff addDefectProd_eq_zero_iff addDefectSum_q_mul_left norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma spec_eq_zero_of_master ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMulInt sum_Ico_divisorSum_mul_eq_sum_Sols Fz Gz Gz_neg Fz_mul_Gz xDivTerm_eq_mul_Fz tent tent_one cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice MuTranslation ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section PolyGeom

lemma summable_polyGeomSeq (d : ℕ) {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    Summable fun k : ℕ => ((k : ℝ) + 1) ^ d * r ^ k := by
  have hF : Summable fun n : ℕ => (n : ℝ) ^ d * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one d
      (by rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt h0)]; exact h1)
  have hshift : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ d * r ^ (k + 1) :=
    (summable_nat_add_iff 1).mpr hF
  have hr' : r ≠ 0 := ne_of_gt h0
  have hcancel : ∀ k : ℕ, r ^ (k + 1) * r⁻¹ = r ^ k := by
    intro k
    rw [pow_succ, mul_assoc, mul_inv_cancel₀ hr', mul_one]
  refine (hshift.mul_right r⁻¹).congr fun k => ?_
  calc ((k + 1 : ℕ) : ℝ) ^ d * r ^ (k + 1) * r⁻¹
      = ((k : ℝ) + 1) ^ d * (r ^ (k + 1) * r⁻¹) := by push_cast; ring
    _ = ((k : ℝ) + 1) ^ d * r ^ k := by rw [hcancel k]

noncomputable def polyGeomBound (d : ℕ) (r : ℝ) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) + 1) ^ d * r ^ k

lemma polyGeomBound_nonneg (d : ℕ) {r : ℝ} (h0 : 0 ≤ r) : 0 ≤ polyGeomBound d r :=
  tsum_nonneg fun k => by positivity

lemma le_polyGeomBound (d : ℕ) {r : ℝ} (h0 : 0 < r) (h1 : r < 1) (k : ℕ) :
    ((k : ℝ) + 1) ^ d * r ^ k ≤ polyGeomBound d r := by
  have hsum := summable_polyGeomSeq d h0 h1
  have hsplit := hsum.sum_add_tsum_nat_add (k + 1)
  have hterm : ((k : ℝ) + 1) ^ d * r ^ k
      ≤ ∑ i ∈ Finset.range (k + 1), ((i : ℝ) + 1) ^ d * r ^ i :=
    Finset.single_le_sum (f := fun i : ℕ => ((i : ℝ) + 1) ^ d * r ^ i)
      (fun i _ => by positivity) (Finset.self_mem_range_succ k)
  have htail : (0 : ℝ) ≤ ∑' i : ℕ, (((i + (k + 1) : ℕ) : ℝ) + 1) ^ d * r ^ (i + (k + 1)) :=
    tsum_nonneg fun i => by positivity
  calc ((k : ℝ) + 1) ^ d * r ^ k
      ≤ ∑ i ∈ Finset.range (k + 1), ((i : ℝ) + 1) ^ d * r ^ i := hterm
    _ ≤ (∑ i ∈ Finset.range (k + 1), ((i : ℝ) + 1) ^ d * r ^ i)
          + ∑' i : ℕ, (((i + (k + 1) : ℕ) : ℝ) + 1) ^ d * r ^ (i + (k + 1)) :=
        le_add_of_nonneg_right htail
    _ = polyGeomBound d r := hsplit

lemma add_one_pow_le_mul_add_one_pow (d M k : ℕ) :
    (((M + k : ℕ) : ℝ) + 1) ^ d ≤ ((M : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ d
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  push_cast
  nlinarith

end PolyGeom

section EnvReindex

private def shiftPairE_C1EnvelopeEngine : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)

private lemma shiftPairE_injective_C1EnvelopeEngine : Function.Injective shiftPairE_C1EnvelopeEngine := by
  intro p p' h
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := p'
  simp only [shiftPairE_C1EnvelopeEngine, Prod.mk.injEq] at h ⊢
  omega

private lemma mem_range_shiftPairE_C1EnvelopeEngine {p : ℕ × ℕ} (h : p.2 ≤ p.1) : p ∈ Set.range shiftPairE_C1EnvelopeEngine :=
  ⟨(p.1 - p.2, p.2), by
    simp only [shiftPairE_C1EnvelopeEngine]
    exact Prod.ext (by omega) rfl⟩

private lemma tsum_prod_eq_tsum_sum_antidiagonalE_C1EnvelopeEngine {f : ℕ × ℕ → K} (hf : Summable f) :
    ∑' p : ℕ × ℕ, f p = ∑' M : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal M, f p := by
  have he := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq f
  rw [← he]
  have hsum : Summable fun x : Σ M : ℕ, (Finset.HasAntidiagonal.antidiagonal M : Finset (ℕ × ℕ)) =>
      f (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd x) := by
    have h1 := (Equiv.summable_iff (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ))).mpr hf
    simpa [Function.comp_def] using h1
  rw [hsum.tsum_sigma]
  refine tsum_congr fun M => ?_
  rw [tsum_fintype, ← Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal M) f]
  exact Finset.sum_congr rfl fun c _ => rfl

private lemma summable_of_shift_bound_factored_C1EnvelopeEngine {f : ℕ × ℕ → K} {g h : ℕ → ℝ}
    (hg : Summable g) (hh : Summable h)
    (hg0 : ∀ n, 0 ≤ g n) (hh0 : ∀ n, 0 ≤ h n)
    (hvanish : ∀ p : ℕ × ℕ, ¬ p.2 ≤ p.1 → f p = 0)
    (hbound : ∀ p : ℕ × ℕ, ‖f (shiftPairE_C1EnvelopeEngine p)‖ ≤ g p.1 * h p.2) :
    Summable f := by
  have hgeom : Summable fun p : ℕ × ℕ => g p.1 * h p.2 :=
    hg.mul_of_nonneg hh hg0 hh0
  have hcomp : Summable fun p : ℕ × ℕ => f (shiftPairE_C1EnvelopeEngine p) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound hgeom)
  have hsupport : ∀ x ∉ Set.range shiftPairE_C1EnvelopeEngine, f x = 0 := by
    intro x hx
    refine hvanish x fun hle => hx (mem_range_shiftPairE_C1EnvelopeEngine hle)
  have hcomp' : Summable (f ∘ shiftPairE_C1EnvelopeEngine) := by exact hcomp
  exact (shiftPairE_injective_C1EnvelopeEngine.summable_iff hsupport).mp hcomp'

end EnvReindex

section EnvFamilies

variable (c : ℕ → ℕ → K) (w q : K)

private noncomputable def hubOddE_C1EnvelopeEngine (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then
    c p.1 p.2 * ((q * w) ^ p.2 - (q * w)⁻¹ ^ p.2) * q ^ p.1 else 0

private noncomputable def alphaOddE_C1EnvelopeEngine (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then c p.1 p.2 * w ^ p.2 * q ^ (p.1 + p.2) else 0

private noncomputable def betaOddE_C1EnvelopeEngine (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then -(c p.1 p.2 * w⁻¹ ^ p.2 * q ^ (p.1 - p.2)) else 0

variable {c w q}

private lemma hubOddE_eq_C1EnvelopeEngine (hq0 : q ≠ 0) (_hw0 : w ≠ 0) (p : ℕ × ℕ) :
    hubOddE_C1EnvelopeEngine c w q p = alphaOddE_C1EnvelopeEngine c w q p + betaOddE_C1EnvelopeEngine c w q p := by
  simp only [hubOddE_C1EnvelopeEngine, alphaOddE_C1EnvelopeEngine, betaOddE_C1EnvelopeEngine]
  by_cases hg : 1 ≤ p.2 ∧ p.2 ≤ p.1
  · rw [if_pos hg, if_pos hg, if_pos hg]
    obtain ⟨j, hj⟩ : ∃ j, p.1 = j + p.2 := ⟨p.1 - p.2, by omega⟩
    rw [hj]
    have hsub : j + p.2 - p.2 = j := by omega
    rw [hsub]
    have hqp : q ^ p.2 ≠ 0 := pow_ne_zero _ hq0
    have hcancel : q ^ p.2 * q⁻¹ ^ p.2 = 1 := by
      rw [inv_pow, mul_inv_cancel₀ hqp]
    have hsplit : (q * w)⁻¹ ^ p.2 = q⁻¹ ^ p.2 * w⁻¹ ^ p.2 := by
      rw [mul_inv, mul_pow]
    rw [hsplit]
    linear_combination (-(c (j + p.2) p.2 * w⁻¹ ^ p.2 * q ^ j)) * hcancel
  · rw [if_neg hg, if_neg hg, if_neg hg]
    ring

variable {B : ℝ} {d : ℕ}

set_option maxHeartbeats 4000000 in
private lemma summable_alphaOddE_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) : Summable (alphaOddE_C1EnvelopeEngine c w q) := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hqwpos : (0 : ℝ) < ‖q‖ * ‖w‖ := mul_pos hqpos (lt_trans one_pos hw)
  refine summable_of_shift_bound_factored_C1EnvelopeEngine
    (g := fun i => B * ((i : ℝ) + 1) ^ d * ‖q‖ ^ i)
    (h := fun k => ((k : ℝ) + 1) ^ d * (‖q‖ * ‖w‖) ^ k)
    (((summable_polyGeomSeq d hqpos hq1).mul_left B).congr fun i => by ring)
    (summable_polyGeomSeq d hqwpos hqw)
    (fun i => by positivity) (fun k => by positivity) ?_ ?_
  · intro p hp
    simp only [alphaOddE_C1EnvelopeEngine]
    exact if_neg fun hg => hp hg.2
  · intro p
    simp only [alphaOddE_C1EnvelopeEngine, shiftPairE_C1EnvelopeEngine]
    by_cases hg : 1 ≤ p.2
    · rw [if_pos ⟨hg, by omega⟩]
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖c (p.1 + p.2) p.2‖ ≤ B * (((p.1 : ℝ) + 1) ^ d * ((p.2 : ℝ) + 1) ^ d) :=
        le_trans (hc _ _)
          (mul_le_mul_of_nonneg_left (add_one_pow_le_mul_add_one_pow d p.1 p.2) hB)
      have h2 : ‖q‖ ^ (p.1 + p.2 + p.2) = ‖q‖ ^ p.1 * ‖q‖ ^ p.2 * ‖q‖ ^ p.2 := by
        rw [← pow_add, ← pow_add]
      have h3 : ‖q‖ ^ p.2 ≤ 1 := pow_le_one₀ (norm_nonneg q) (le_of_lt hq1)
      calc ‖c (p.1 + p.2) p.2‖ * ‖w‖ ^ p.2 * ‖q‖ ^ (p.1 + p.2 + p.2)
          = ‖c (p.1 + p.2) p.2‖ * (‖q‖ ^ p.1 * (‖q‖ * ‖w‖) ^ p.2 * ‖q‖ ^ p.2) := by
            rw [h2, mul_pow]
            ring
        _ ≤ (B * (((p.1 : ℝ) + 1) ^ d * ((p.2 : ℝ) + 1) ^ d))
              * (‖q‖ ^ p.1 * (‖q‖ * ‖w‖) ^ p.2 * 1) := by
            refine mul_le_mul h1 ?_ (by positivity) (by positivity)
            refine mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (B * ((p.1 : ℝ) + 1) ^ d * ‖q‖ ^ p.1)
              * (((p.2 : ℝ) + 1) ^ d * (‖q‖ * ‖w‖) ^ p.2) := by ring
    · rw [if_neg fun hcon => hg hcon.1, norm_zero]
      positivity

set_option maxHeartbeats 4000000 in
private lemma summable_betaOddE_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) : Summable (betaOddE_C1EnvelopeEngine c w q) := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hw0 : w ≠ 0 := ne_zero_of_one_lt_norm hw
  have hρ : ‖w⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hw
  have hρpos : (0 : ℝ) < ‖w⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hw0)
  refine summable_of_shift_bound_factored_C1EnvelopeEngine
    (g := fun i => B * ((i : ℝ) + 1) ^ d * ‖q‖ ^ i)
    (h := fun k => ((k : ℝ) + 1) ^ d * ‖w⁻¹‖ ^ k)
    (((summable_polyGeomSeq d hqpos hq1).mul_left B).congr fun i => by ring)
    (summable_polyGeomSeq d hρpos hρ)
    (fun i => by positivity) (fun k => by positivity) ?_ ?_
  · intro p hp
    simp only [betaOddE_C1EnvelopeEngine]
    exact if_neg fun hg => hp hg.2
  · intro p
    simp only [betaOddE_C1EnvelopeEngine, shiftPairE_C1EnvelopeEngine]
    by_cases hg : 1 ≤ p.2
    · rw [if_pos ⟨hg, by omega⟩]
      have h0 : p.1 + p.2 - p.2 = p.1 := by omega
      rw [h0, norm_neg, norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖c (p.1 + p.2) p.2‖ ≤ B * (((p.1 : ℝ) + 1) ^ d * ((p.2 : ℝ) + 1) ^ d) :=
        le_trans (hc _ _)
          (mul_le_mul_of_nonneg_left (add_one_pow_le_mul_add_one_pow d p.1 p.2) hB)
      calc ‖c (p.1 + p.2) p.2‖ * ‖w⁻¹‖ ^ p.2 * ‖q‖ ^ p.1
          ≤ (B * (((p.1 : ℝ) + 1) ^ d * ((p.2 : ℝ) + 1) ^ d)) * ‖w⁻¹‖ ^ p.2 * ‖q‖ ^ p.1 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (B * ((p.1 : ℝ) + 1) ^ d * ‖q‖ ^ p.1)
              * (((p.2 : ℝ) + 1) ^ d * ‖w⁻¹‖ ^ p.2) := by ring
    · rw [if_neg fun hcon => hg hcon.1, norm_zero]
      positivity

private lemma summable_hubOddE_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) : Summable (hubOddE_C1EnvelopeEngine c w q) := by
  have hw0 : w ≠ 0 := ne_zero_of_one_lt_norm hw
  exact ((summable_alphaOddE_C1EnvelopeEngine hB hc hq0 hw hqw).add
    (summable_betaOddE_C1EnvelopeEngine hB hc hq0 hw hqw)).congr fun p => (hubOddE_eq_C1EnvelopeEngine hq0 hw0 p).symm

end EnvFamilies

section EnvRegroup

variable {c : ℕ → ℕ → K} {w q : K} {B : ℝ} {d : ℕ}

set_option maxHeartbeats 4000000 in
private lemma tsum_alphaOddE_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    ∑' p : ℕ × ℕ, alphaOddE_C1EnvelopeEngine c w q p = ∑' M : ℕ, specAlpha c w M * q ^ M := by
  rw [tsum_prod_eq_tsum_sum_antidiagonalE_C1EnvelopeEngine (summable_alphaOddE_C1EnvelopeEngine hB hc hq0 hw hqw)]
  refine tsum_congr fun M => ?_
  simp only [specAlpha]
  rw [Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpM : p.1 + p.2 = M := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  simp only [alphaOddE_C1EnvelopeEngine]
  by_cases hg : 1 ≤ p.2 ∧ p.2 ≤ p.1
  · rw [if_pos hg, if_pos hg, hpM]
  · rw [if_neg hg, if_neg hg, zero_mul]

set_option maxHeartbeats 4000000 in
private lemma tsum_betaOddE_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    ∑' p : ℕ × ℕ, betaOddE_C1EnvelopeEngine c w q p = ∑' M : ℕ, (-specTail c w M) * q ^ M := by
  have hsupport : Function.support (betaOddE_C1EnvelopeEngine c w q) ⊆ Set.range shiftPairE_C1EnvelopeEngine := by
    intro p hp
    by_contra hcon
    refine hp ?_
    simp only [betaOddE_C1EnvelopeEngine]
    refine if_neg fun hg => hcon (mem_range_shiftPairE_C1EnvelopeEngine hg.2)
  rw [← shiftPairE_injective_C1EnvelopeEngine.tsum_eq hsupport]
  have hcomp : Summable fun p : ℕ × ℕ => betaOddE_C1EnvelopeEngine c w q (shiftPairE_C1EnvelopeEngine p) :=
    (summable_betaOddE_C1EnvelopeEngine hB hc hq0 hw hqw).comp_injective shiftPairE_injective_C1EnvelopeEngine
  rw [hcomp.tsum_prod]
  refine tsum_congr fun M => ?_
  simp only [specTail]
  rw [neg_mul, ← tsum_mul_right, ← tsum_neg]
  refine tsum_congr fun k => ?_
  simp only [betaOddE_C1EnvelopeEngine, shiftPairE_C1EnvelopeEngine]
  by_cases hk : 1 ≤ k
  · rw [if_pos ⟨hk, by omega⟩, if_pos hk]
    have h0 : M + k - k = M := by omega
    rw [h0]
  · rw [if_neg fun hcon => hk hcon.1, if_neg hk, zero_mul, neg_zero]

set_option maxHeartbeats 4000000 in
private lemma tsum_hubOddE_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    ∑' p : ℕ × ℕ, hubOddE_C1EnvelopeEngine c w q p
      = ∑' M : ℕ,
          (∑ k ∈ Finset.Icc 1 M, c M k * ((q * w) ^ k - (q * w)⁻¹ ^ k)) * q ^ M := by
  rw [(summable_hubOddE_C1EnvelopeEngine hB hc hq0 hw hqw).tsum_prod]
  refine tsum_congr fun N => ?_
  have hvanish : ∀ k ∉ Finset.Icc 1 N, hubOddE_C1EnvelopeEngine c w q (N, k) = 0 := by
    intro k hk
    simp only [hubOddE_C1EnvelopeEngine]
    refine if_neg fun hg => hk (Finset.mem_Icc.mpr ⟨hg.1, hg.2⟩)
  rw [tsum_eq_sum hvanish, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  simp only [hubOddE_C1EnvelopeEngine]
  rw [if_pos ⟨hk'.1, hk'.2⟩]

end EnvRegroup

section EnvSpecBounds

variable {c : ℕ → ℕ → K} {w q : K} {B : ℝ} {d : ℕ}

private lemma norm_specAlpha_le_env_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) (hw : 1 ≤ ‖w‖) (M : ℕ) :
    ‖specAlpha c w M‖ ≤ B * ((M : ℝ) + 1) ^ d * ‖w‖ ^ M := by
  refine norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (mul_nonneg hB (by positivity)) (by positivity)) fun p hp => ?_
  have hmem := Finset.mem_filter.mp hp
  have hanti := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem.1
  have hp1M : p.1 ≤ M := by omega
  have hp2M : p.2 ≤ M := by omega
  rw [norm_mul, norm_pow]
  have h1 : ‖c p.1 p.2‖ ≤ B * ((p.1 : ℝ) + 1) ^ d := hc _ _
  have h1' : B * ((p.1 : ℝ) + 1) ^ d ≤ B * ((M : ℝ) + 1) ^ d := by
    refine mul_le_mul_of_nonneg_left ?_ hB
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have : (p.1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hp1M
    linarith
  have h2 : ‖w‖ ^ p.2 ≤ ‖w‖ ^ M := pow_le_pow_right₀ hw hp2M
  calc ‖c p.1 p.2‖ * ‖w‖ ^ p.2
      ≤ (B * ((M : ℝ) + 1) ^ d) * ‖w‖ ^ M := by
        refine mul_le_mul (le_trans h1 h1') h2 (by positivity) ?_
        exact mul_nonneg hB (by positivity)
    _ = B * ((M : ℝ) + 1) ^ d * ‖w‖ ^ M := by ring

private lemma norm_specTail_le_env_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hwr : ‖w⁻¹‖ ≤ r) (M : ℕ) :
    ‖specTail c w M‖ ≤ B * ((M : ℝ) + 1) ^ d * polyGeomBound d r := by
  have hC0 : 0 ≤ B * ((M : ℝ) + 1) ^ d * polyGeomBound d r :=
    mul_nonneg (mul_nonneg hB (by positivity)) (polyGeomBound_nonneg d (le_of_lt hr0))
  refine norm_tsum_le_of_forall_le_of_nonneg hC0 fun k => ?_
  by_cases hk : 1 ≤ k
  · rw [if_pos hk, norm_mul, norm_pow]
    have h1 : ‖c (M + k) k‖ ≤ B * (((M : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d) :=
      le_trans (hc _ _)
        (mul_le_mul_of_nonneg_left (add_one_pow_le_mul_add_one_pow d M k) hB)
    have h2 : ‖w⁻¹‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg _) hwr k
    calc ‖c (M + k) k‖ * ‖w⁻¹‖ ^ k
        ≤ (B * (((M : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d)) * r ^ k := by
          refine mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (B * ((M : ℝ) + 1) ^ d) * (((k : ℝ) + 1) ^ d * r ^ k) := by ring
      _ ≤ (B * ((M : ℝ) + 1) ^ d) * polyGeomBound d r := by
          refine mul_le_mul_of_nonneg_left (le_polyGeomBound d hr0 hr1 k) ?_
          exact mul_nonneg hB (by positivity)
      _ = B * ((M : ℝ) + 1) ^ d * polyGeomBound d r := by ring
  · rw [if_neg hk, norm_zero]
    exact hC0

private lemma norm_spectatorRows_le_env_C1EnvelopeEngine {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (hB : 0 ≤ B) (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    {v : K} (hv : ‖v‖ = 1) (M k : ℕ) :
    ‖spectatorRows s a v M k‖ ≤ B * ((M : ℝ) + 1) ^ d :=
  norm_finsetSum_mul_zpow_le_of_norm_eq_one hv
    (mul_nonneg hB (by positivity)) (fun j _ => ha M k j)

private lemma summable_specAlpha_mul_pow_env_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    Summable fun M : ℕ => specAlpha c w M * q ^ M := by
  have hqwpos : (0 : ℝ) < ‖q‖ * ‖w‖ :=
    mul_pos (norm_pos_iff.mpr hq0) (lt_trans one_pos hw)
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_)
    ((summable_polyGeomSeq d hqwpos hqw).mul_left B))
  rw [norm_mul, norm_pow]
  have h1 := norm_specAlpha_le_env_C1EnvelopeEngine hB hc (le_of_lt hw) M
  have h2 : ‖w‖ ^ M * ‖q‖ ^ M = (‖q‖ * ‖w‖) ^ M := by rw [mul_pow]; ring
  calc ‖specAlpha c w M‖ * ‖q‖ ^ M
      ≤ (B * ((M : ℝ) + 1) ^ d * ‖w‖ ^ M) * ‖q‖ ^ M :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = B * (((M : ℝ) + 1) ^ d * (‖q‖ * ‖w‖) ^ M) := by rw [← h2]; ring

private lemma summable_specTail_mul_pow_env_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    Summable fun M : ℕ => specTail c w M * q ^ M := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hw0 : w ≠ 0 := ne_zero_of_one_lt_norm hw
  have hρpos : (0 : ℝ) < ‖w⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hw0)
  have hρ : ‖w⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hw
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_)
    ((summable_polyGeomSeq d hqpos hq1).mul_left (B * polyGeomBound d ‖w⁻¹‖)))
  rw [norm_mul, norm_pow]
  have h1 := norm_specTail_le_env_C1EnvelopeEngine hB hc hρpos hρ le_rfl M
  calc ‖specTail c w M‖ * ‖q‖ ^ M
      ≤ (B * ((M : ℝ) + 1) ^ d * polyGeomBound d ‖w⁻¹‖) * ‖q‖ ^ M :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = B * polyGeomBound d ‖w⁻¹‖ * (((M : ℝ) + 1) ^ d * ‖q‖ ^ M) := by ring

private lemma summable_specOdd_series_env_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    Summable fun M : ℕ => (specAlpha c w M - specTail c w M) * q ^ M := by
  refine ((summable_specAlpha_mul_pow_env_C1EnvelopeEngine hB hc hq0 hw hqw).sub
    (summable_specTail_mul_pow_env_C1EnvelopeEngine hB hc hq0 hw hqw)).congr fun M => ?_
  ring

end EnvSpecBounds

section EnvAbstractMaster

set_option maxHeartbeats 4000000 in

theorem master_of_hasSum_qshift_odd_envelope {B : ℝ} {d : ℕ} (hB : 0 ≤ B) (c : ℕ → ℕ → K)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) {g : K → K → K}
    (hinv : ∀ q w : K, q ≠ 0 → 1 < ‖w‖ → ‖q‖ * ‖w‖ < 1 → g q (q * w) = g q w)
    (hrepr : ∀ q w : K, q ≠ 0 → ‖q‖ < ‖w‖ → ‖q‖ * ‖w‖ < 1 → ‖w‖ ≠ 1 →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k - w⁻¹ ^ k)) * q ^ M) (g q w)) :
    ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k - w⁻¹ ^ k)
        = specAlpha c w M - specTail c w M := by
  intro M w hw
  have hw0 : w ≠ 0 := ne_zero_of_one_lt_norm hw
  have hwpos : (0 : ℝ) < ‖w‖ := lt_trans one_pos hw
  have hwne1 : ‖w‖ ≠ 1 := ne_of_gt hw

  have hq₀0 : w⁻¹ * w⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hw0) (inv_ne_zero hw0)
  have hwinv_lt : ‖w⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hw
  have hwinv_pos : (0 : ℝ) < ‖w⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hw0)
  have hq₀norm : ‖w⁻¹ * w⁻¹‖ = ‖w⁻¹‖ * ‖w⁻¹‖ := norm_mul _ _
  have hq₀1 : ‖w⁻¹ * w⁻¹‖ < 1 := by
    rw [hq₀norm]
    nlinarith

  have hregion : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ → ‖q‖ * ‖w‖ < 1 := by
    intro q hq hqle
    have h1 : ‖w⁻¹‖ * ‖w‖ = 1 := by
      rw [norm_inv]
      field_simp
    have h2 : ‖q‖ ≤ ‖w⁻¹‖ * ‖w⁻¹‖ := by rwa [hq₀norm] at hqle
    nlinarith
  have hqlt_of : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ → ‖q‖ < ‖w‖ := by
    intro q hq hqle
    have h1 : ‖q‖ < 1 := lt_of_le_of_lt hqle hq₀1
    linarith

  have ha : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ →
      Summable fun N => (∑ k ∈ Finset.Icc 1 N, c N k * (w ^ k - w⁻¹ ^ k)) * q ^ N := by
    intro q hq hqle
    exact (hrepr q w hq (hqlt_of q hq hqle) (hregion q hq hqle) hwne1).summable
  have hb : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ →
      Summable fun N => (specAlpha c w N - specTail c w N) * q ^ N := by
    intro q hq hqle
    exact summable_specOdd_series_env_C1EnvelopeEngine hB hc hq hw (hregion q hq hqle)
  have heq : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ →
      ∑' N, (∑ k ∈ Finset.Icc 1 N, c N k * (w ^ k - w⁻¹ ^ k)) * q ^ N
        = ∑' N, (specAlpha c w N - specTail c w N) * q ^ N := by
    intro q hq hqle
    have hqw : ‖q‖ * ‖w‖ < 1 := hregion q hq hqle
    have hq1 : ‖q‖ < 1 := lt_of_le_of_lt hqle hq₀1
    have hqlt : ‖q‖ < ‖w‖ := hqlt_of q hq hqle
    have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq

    have hqw_norm : ‖q * w‖ = ‖q‖ * ‖w‖ := norm_mul q w
    have hqw_lt1 : ‖q * w‖ < 1 := by rw [hqw_norm]; exact hqw
    have hqw_gt : ‖q‖ < ‖q * w‖ := by
      rw [hqw_norm]
      nlinarith [mul_pos hqpos (sub_pos.mpr hw)]
    have hq_qw : ‖q‖ * ‖q * w‖ < 1 := by
      rw [hqw_norm]
      have h := mul_lt_mul_of_pos_left hqw hqpos
      rw [mul_one] at h
      linarith
    have hqw_ne1 : ‖q * w‖ ≠ 1 := ne_of_lt hqw_lt1

    have hX := hrepr q w hq hqlt hqw hwne1
    have hXq := hrepr q (q * w) hq hqw_gt hq_qw hqw_ne1

    have hSα := summable_specAlpha_mul_pow_env_C1EnvelopeEngine hB hc hq hw hqw
    have hSτ' : Summable fun M : ℕ => (-specTail c w M) * q ^ M :=
      ((summable_specTail_mul_pow_env_C1EnvelopeEngine hB hc hq hw hqw).neg).congr fun M => by ring

    calc ∑' N, (∑ k ∈ Finset.Icc 1 N, c N k * (w ^ k - w⁻¹ ^ k)) * q ^ N
        = g q w := hX.tsum_eq
      _ = g q (q * w) := (hinv q w hq hw hqw).symm
      _ = ∑' N, (∑ k ∈ Finset.Icc 1 N, c N k * ((q * w) ^ k - (q * w)⁻¹ ^ k)) * q ^ N :=
          hXq.tsum_eq.symm
      _ = ∑' p : ℕ × ℕ, hubOddE_C1EnvelopeEngine c w q p := (tsum_hubOddE_C1EnvelopeEngine hB hc hq hw hqw).symm
      _ = ∑' p : ℕ × ℕ, (alphaOddE_C1EnvelopeEngine c w q p + betaOddE_C1EnvelopeEngine c w q p) :=
          tsum_congr fun p => hubOddE_eq_C1EnvelopeEngine hq hw0 p
      _ = (∑' p : ℕ × ℕ, alphaOddE_C1EnvelopeEngine c w q p) + ∑' p : ℕ × ℕ, betaOddE_C1EnvelopeEngine c w q p :=
          (summable_alphaOddE_C1EnvelopeEngine hB hc hq hw hqw).tsum_add (summable_betaOddE_C1EnvelopeEngine hB hc hq hw hqw)
      _ = (∑' M, specAlpha c w M * q ^ M) + ∑' M, (-specTail c w M) * q ^ M := by
          rw [tsum_alphaOddE_C1EnvelopeEngine hB hc hq hw hqw, tsum_betaOddE_C1EnvelopeEngine hB hc hq hw hqw]
      _ = ∑' M, (specAlpha c w M * q ^ M + (-specTail c w M) * q ^ M) := by
          rw [hSα.tsum_add hSτ']
      _ = ∑' N, (specAlpha c w N - specTail c w N) * q ^ N :=
          tsum_congr fun N => by ring

  have hε : (0 : ℝ) < ‖w⁻¹ * w⁻¹‖ := norm_pos_iff.mpr hq₀0
  refine coeff_eq_of_hasSum_eq
    (A := fun N => ∑ k ∈ Finset.Icc 1 N, c N k * (w ^ k - w⁻¹ ^ k))
    (Bc := fun N => specAlpha c w N - specTail c w N)
    hε (fun q' hq'0 hq'lt => ?_) M
  have hq'le : ‖q'‖ ≤ ‖w⁻¹ * w⁻¹‖ := le_of_lt hq'lt
  refine ⟨g q' w, hrepr q' w hq'0 (hqlt_of q' hq'0 hq'le) (hregion q' hq'0 hq'le) hwne1, ?_⟩
  have h1 : (∑' N, (specAlpha c w N - specTail c w N) * q' ^ N) = g q' w := by
    rw [← heq q' hq'0 hq'le,
      (hrepr q' w hq'0 (hqlt_of q' hq'0 hq'le) (hregion q' hq'0 hq'le) hwne1).tsum_eq]
  exact h1 ▸ (hb q' hq'0 hq'le).hasSum

end EnvAbstractMaster

section EnvBoundedDescent

variable {c : ℕ → ℕ → K} {B : ℝ} {d : ℕ}

set_option maxHeartbeats 4000000 in

private lemma spec_eq_zero_of_diamond_odd_env_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) {M k₀ : ℕ}
    (hk₀1 : 1 ≤ k₀) (hk₀M : k₀ ≤ M)
    (hdiamond : ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k - w⁻¹ ^ k) = -specTail c w M)
    (hbig : ∀ k', k₀ < k' → k' ≤ M → c M k' = 0) :
    c M k₀ = 0 := by

  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
  have hx0 : x ≠ 0 := ne_zero_of_one_lt_norm hx
  have hxinv : ‖x⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hx
  have hxinv_pos : (0 : ℝ) < ‖x⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hx0)
  set v : ℕ → K := fun t => x ^ (t + 1) with hv
  have hv0 : ∀ t, v t ≠ 0 := fun t => pow_ne_zero _ hx0
  have hvnorm : ∀ t, ‖v t‖ = ‖x‖ ^ (t + 1) := fun t => by rw [hv]; exact norm_pow x (t + 1)
  have hvbig : ∀ t, 1 < ‖v t‖ := by
    intro t
    rw [hvnorm t]
    exact one_lt_pow₀ hx (Nat.succ_ne_zero t)
  have hvinvnorm : ∀ t, ‖(v t)⁻¹‖ = ‖x⁻¹‖ ^ (t + 1) := by
    intro t
    rw [norm_inv, hvnorm t, norm_inv, inv_pow]
  have hvinvle : ∀ t, ‖(v t)⁻¹‖ ≤ ‖x⁻¹‖ := by
    intro t
    rw [hvinvnorm t]
    calc ‖x⁻¹‖ ^ (t + 1) = ‖x⁻¹‖ ^ t * ‖x⁻¹‖ := pow_succ _ _
      _ ≤ 1 * ‖x⁻¹‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact pow_le_one₀ (norm_nonneg _) (le_of_lt hxinv)
      _ = ‖x⁻¹‖ := one_mul _

  set Cst : ℝ := B * ((M : ℝ) + 1) ^ d * polyGeomBound d ‖x⁻¹‖ with hCst

  set f : ℕ → K := fun t => -specTail c (v t) M * (v t)⁻¹ ^ k₀ with hf

  have hf0 : Tendsto f atTop (nhds 0) := by
    have hbound : ∀ t, ‖f t‖ ≤ Cst * (‖x⁻¹‖ ^ k₀) ^ (t + 1) := by
      intro t
      rw [hf]
      simp only []
      rw [norm_mul, norm_neg, norm_pow]
      have h1 : ‖specTail c (v t) M‖ ≤ Cst := by
        rw [hCst]
        exact norm_specTail_le_env_C1EnvelopeEngine hB hc hxinv_pos hxinv (hvinvle t) M
      have h2 : ‖(v t)⁻¹‖ ^ k₀ = (‖x⁻¹‖ ^ (t + 1)) ^ k₀ := by rw [hvinvnorm t]
      have h3 : (‖x⁻¹‖ ^ (t + 1)) ^ k₀ = (‖x⁻¹‖ ^ k₀) ^ (t + 1) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have h4 : (0 : ℝ) ≤ ‖(v t)⁻¹‖ ^ k₀ := pow_nonneg (norm_nonneg _) _
      calc ‖specTail c (v t) M‖ * ‖(v t)⁻¹‖ ^ k₀ ≤ Cst * ‖(v t)⁻¹‖ ^ k₀ :=
            mul_le_mul_of_nonneg_right h1 h4
        _ = Cst * (‖x⁻¹‖ ^ k₀) ^ (t + 1) := by rw [h2, h3]
    have hratio : ‖x⁻¹‖ ^ k₀ < 1 :=
      pow_lt_one₀ (norm_nonneg _) hxinv (by omega)
    have hgeo : Tendsto (fun t : ℕ => Cst * (‖x⁻¹‖ ^ k₀) ^ (t + 1)) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => (‖x⁻¹‖ ^ k₀) ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg (norm_nonneg _) _) hratio
      have h2 : Tendsto (fun t : ℕ => (‖x⁻¹‖ ^ k₀) ^ (t + 1)) atTop (nhds 0) :=
        h1.comp (tendsto_add_atTop_nat 1)
      have h3 := h2.const_mul Cst
      simpa using h3
    exact squeeze_zero_norm hbound hgeo

  have hflim : Tendsto f atTop (nhds (c M k₀)) := by
    have hfeq : ∀ t, f t
        = ∑ k ∈ Finset.Icc 1 M, c M k * ((v t) ^ k - (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀ := by
      intro t
      rw [hf]
      simp only []
      rw [← hdiamond (v t) (hvbig t), Finset.sum_mul]
    have hterm : ∀ k ∈ Finset.Icc 1 M,
        Tendsto (fun t => c M k * ((v t) ^ k - (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀)
          atTop (nhds (if k = k₀ then c M k₀ else 0)) := by
      intro k hk
      have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hpt : ∀ t, c M k * ((v t) ^ k - (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀
          = c M k * ((x ^ k * (x ^ k₀)⁻¹) ^ (t + 1) - ((x ^ (k + k₀))⁻¹) ^ (t + 1)) := by
        intro t
        rw [hv]
        simp only []
        have hxp : x ^ (t + 1) ≠ 0 := pow_ne_zero _ hx0
        field_simp
        ring
      rcases lt_trichotomy k k₀ with hlt | heq | hgt
      · rw [if_neg (Nat.ne_of_lt hlt)]
        have hw1 : ‖x ^ k * (x ^ k₀)⁻¹‖ < 1 := by
          rw [norm_mul, norm_inv, norm_pow, norm_pow, ← div_eq_mul_inv]
          rw [div_lt_one (pow_pos (lt_trans one_pos hx) k₀)]
          exact pow_lt_pow_right₀ hx hlt
        have hz : ‖(x ^ (k + k₀))⁻¹‖ < 1 := by
          rw [norm_inv, inv_lt_one_iff₀]
          right
          rw [norm_pow]
          exact one_lt_pow₀ hx (by omega)
        have hwlim : Tendsto (fun t : ℕ => (x ^ k * (x ^ k₀)⁻¹) ^ (t + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hw1).comp (tendsto_add_atTop_nat 1)
        have hzlim : Tendsto (fun t : ℕ => ((x ^ (k + k₀))⁻¹) ^ (t + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz).comp (tendsto_add_atTop_nat 1)
        have hlim : Tendsto (fun t => c M k
            * ((x ^ k * (x ^ k₀)⁻¹) ^ (t + 1) - ((x ^ (k + k₀))⁻¹) ^ (t + 1)))
            atTop (nhds (c M k * (0 - 0))) :=
          (hwlim.sub hzlim).const_mul _
        rw [sub_zero, mul_zero] at hlim
        refine Tendsto.congr (fun t => (hpt t).symm) hlim
      · subst heq
        rw [if_pos rfl]
        have hw1 : x ^ k * (x ^ k)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hx0)
        have hz : ‖(x ^ (k + k))⁻¹‖ < 1 := by
          rw [norm_inv, inv_lt_one_iff₀]
          right
          rw [norm_pow]
          exact one_lt_pow₀ hx (by omega)
        have hzlim : Tendsto (fun t : ℕ => ((x ^ (k + k))⁻¹) ^ (t + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz).comp (tendsto_add_atTop_nat 1)
        have hlim : Tendsto (fun t => c M k
            * ((x ^ k * (x ^ k)⁻¹) ^ (t + 1) - ((x ^ (k + k))⁻¹) ^ (t + 1)))
            atTop (nhds (c M k * (1 - 0))) := by
          have h1 : Tendsto (fun t : ℕ => (x ^ k * (x ^ k)⁻¹) ^ (t + 1)) atTop (nhds 1) := by
            simp only [hw1, one_pow]
            exact tendsto_const_nhds
          exact (h1.sub hzlim).const_mul _
        rw [sub_zero, mul_one] at hlim
        refine Tendsto.congr (fun t => (hpt t).symm) hlim
      · rw [if_neg (by omega)]
        have hzero : c M k = 0 := hbig k hgt hkM
        have hconst : ∀ t, c M k * ((v t) ^ k - (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀ = 0 := by
          intro t
          rw [hzero]
          simp
        refine Tendsto.congr (fun t => (hconst t).symm) tendsto_const_nhds
    have hsum : Tendsto (fun t => ∑ k ∈ Finset.Icc 1 M,
        c M k * ((v t) ^ k - (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀)
        atTop (nhds (∑ k ∈ Finset.Icc 1 M, if k = k₀ then c M k₀ else 0)) :=
      tendsto_finsetSum _ hterm
    have hcollapse : (∑ k ∈ Finset.Icc 1 M, if k = k₀ then c M k₀ else 0) = c M k₀ := by
      rw [Finset.sum_ite_eq' (Finset.Icc 1 M) k₀ (fun _ => c M k₀)]
      rw [if_pos (Finset.mem_Icc.mpr ⟨hk₀1, hk₀M⟩)]
    rw [hcollapse] at hsum
    exact Tendsto.congr (fun t => (hfeq t).symm) hsum
  exact tendsto_nhds_unique hflim hf0

private lemma spec_row_eq_zero_of_diamond_odd_env_C1EnvelopeEngine (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) {M : ℕ}
    (hdiamond : ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k - w⁻¹ ^ k) = -specTail c w M) :
    ∀ k, 1 ≤ k → k ≤ M → c M k = 0 := by
  have hcol : ∀ e j : ℕ, 1 ≤ j → j ≤ M → M ≤ j + e → c M j = 0 := by
    intro e
    induction e with
    | zero =>
        intro j h1 h2 hd
        have hjM : j = M := by omega
        subst hjM
        exact spec_eq_zero_of_diamond_odd_env_C1EnvelopeEngine hB hc h1 le_rfl hdiamond
          (fun k' hk' hk'' => absurd hk'' (by omega))
    | succ e ihd =>
        intro j h1 h2 hd
        rcases (by omega : M ≤ j + e ∨ j + e < M) with h | h
        · exact ihd j h1 h2 h
        · refine spec_eq_zero_of_diamond_odd_env_C1EnvelopeEngine hB hc h1 h2 hdiamond fun k' hk' hk'' => ?_
          exact ihd k' (by omega) hk'' (by omega)
  intro k h1 h2
  exact hcol M k h1 h2 (by omega)

theorem spec_eq_zero_of_master_odd_envelope (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hmaster : ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k - w⁻¹ ^ k)
        = specAlpha c w M - specTail c w M) :
    ∀ N k : ℕ, 1 ≤ k → k ≤ N → c N k = 0 := by
  suffices h : ∀ R N k : ℕ, N ≤ R → 1 ≤ k → k ≤ N → c N k = 0 by
    intro N k h1 h2
    exact h N N k le_rfl h1 h2
  intro R
  induction R with
  | zero =>
      intro N k hNR h1 h2
      omega
  | succ R ihR =>
      intro N k hNR h1 h2
      rcases Nat.lt_or_ge N (R + 1) with hN | hN
      · exact ihR N k (by omega) h1 h2
      have hNeq : N = R + 1 := by omega
      have hdiamond : ∀ w : K, 1 < ‖w‖ →
          ∑ j ∈ Finset.Icc 1 N, c N j * (w ^ j - w⁻¹ ^ j) = -specTail c w N := by
        intro w hw
        have h1' := hmaster N w hw
        have hα : specAlpha c w N = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have hmem := Finset.mem_filter.mp hp
          have hanti := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem.1
          have hp1 : 1 ≤ p.2 := hmem.2.1
          have hp2 : p.2 ≤ p.1 := hmem.2.2
          have hlow : c p.1 p.2 = 0 := by
            refine ihR p.1 p.2 (by omega) hp1 hp2
          rw [hlow]
          simp
        rw [hα, zero_sub] at h1'
        exact h1'
      exact spec_row_eq_zero_of_diamond_odd_env_C1EnvelopeEngine hB hc hdiamond k h1 h2

end EnvBoundedDescent

section EnvEngineWiring

theorem eq_zero_of_master_rows_odd_envelope {B : ℝ} {d : ℕ} {c : ℕ → ℕ → K} {q u g : K}
    (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hmaster : ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k - w⁻¹ ^ k)
        = specAlpha c w M - specTail c w M)
    (hrepr : HasSum (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k - u⁻¹ ^ k)) * q ^ M) g) :
    g = 0 := by
  have hzero := spec_eq_zero_of_master_odd_envelope hB hc hmaster
  have hfun : (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k - u⁻¹ ^ k)) * q ^ M) = fun _ => 0 := by
    funext M
    have hsum0 : ∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k - u⁻¹ ^ k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' := Finset.mem_Icc.mp hk
      rw [hzero M k hk'.1 hk'.2, zero_mul]
    rw [hsum0, zero_mul]
  rw [hfun] at hrepr
  exact hrepr.unique hasSum_zero

end EnvEngineWiring

section EnvSpectatorUpgrade

variable {q : K}

theorem rows_eval_eq_zero_of_master_at_spectators_odd_envelope
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hmaster : ∀ n : ℕ, ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M,
          spectatorRows s a (unitSpectator q n) M k * (w ^ k - w⁻¹ ^ k)
        = specAlpha (spectatorRows s a (unitSpectator q n)) w M
          - specTail (spectatorRows s a (unitSpectator q n)) w M) :
    ∀ M k : ℕ, 1 ≤ k → k ≤ M → ∀ v : K, v ≠ 0 → ∑ j ∈ s M k, a M k j * v ^ j = 0 := by
  intro M k hk1 hkM
  have hvan : ∀ n : ℕ, ∑ j ∈ s M k, a M k j * (unitSpectator q n) ^ j = 0 := by
    intro n
    have hbound : ∀ N k', ‖spectatorRows s a (unitSpectator q n) N k'‖
        ≤ B * ((N : ℝ) + 1) ^ d :=
      fun N k' => norm_spectatorRows_le_env_C1EnvelopeEngine hB ha (norm_unitSpectator hq0 hq n) N k'
    exact spec_eq_zero_of_master_odd_envelope hB hbound (hmaster n) M k hk1 hkM
  refine laurent_eval_eq_zero_of_infinite_roots
    (Set.infinite_range_of_injective (unitSpectator_injective hq0 hq)) ?_ ?_
  · rintro v ⟨n, rfl⟩
    exact unitSpectator_ne_zero hq0 hq n
  · rintro v ⟨n, rfl⟩
    exact hvan n

end EnvSpectatorUpgrade

section EnvD1Conclusions

variable {q u v : K}

theorem addDefectDiff_eq_zero_of_rows_odd_envelope {B : ℝ} {d : ℕ} {c : ℕ → ℕ → K}
    (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hmaster : ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k - w⁻¹ ^ k)
        = specAlpha c w M - specTail c w M)
    (hrepr : HasSum (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k - u⁻¹ ^ k)) * q ^ M) (addDefectDiff q u v)) :
    addDefectDiff q u v = 0 :=
  eq_zero_of_master_rows_odd_envelope hB hc hmaster hrepr

private lemma laurentRows_repr_eq_zero_odd_env_C1EnvelopeEngine {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (hzero : ∀ M k : ℕ, 1 ≤ k → k ≤ M → ∀ v : K, v ≠ 0 →
      ∑ j ∈ s M k, a M k j * v ^ j = 0)
    (hv0 : v ≠ 0) :
    (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v ^ j) * (u ^ k - u⁻¹ ^ k)) * q ^ M)
      = fun _ => 0 := by
  funext M
  have hsum0 : ∑ k ∈ Finset.Icc 1 M,
      (∑ j ∈ s M k, a M k j * v ^ j) * (u ^ k - u⁻¹ ^ k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' := Finset.mem_Icc.mp hk
    rw [hzero M k hk'.1 hk'.2 v hv0, zero_mul]
  rw [hsum0, zero_mul]

theorem addDefectDiff_eq_zero_of_laurentRows_odd_envelope (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hmaster : ∀ n : ℕ, ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M,
          spectatorRows s a (unitSpectator q n) M k * (w ^ k - w⁻¹ ^ k)
        = specAlpha (spectatorRows s a (unitSpectator q n)) w M
          - specTail (spectatorRows s a (unitSpectator q n)) w M)
    (hv0 : v ≠ 0)
    (hrepr : HasSum (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v ^ j) * (u ^ k - u⁻¹ ^ k)) * q ^ M)
      (addDefectDiff q u v)) :
    addDefectDiff q u v = 0 := by
  have hzero := rows_eval_eq_zero_of_master_at_spectators_odd_envelope hq0 hq hB ha hmaster
  rw [laurentRows_repr_eq_zero_odd_env_C1EnvelopeEngine hzero hv0] at hrepr
  exact hrepr.unique hasSum_zero

set_option maxHeartbeats 4000000 in

theorem addDefectDiff_eq_zero_of_rowExpansion_odd_envelope {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hexp : ∀ q' u' v' : K, ExpansionRegion q' u' v' →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M,
            (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k - u'⁻¹ ^ k)) * q' ^ M)
        (addDefectDiff q' u' v'))
    (hreg : ExpansionRegion q u v) :
    addDefectDiff q u v = 0 := by
  have hq0 : q ≠ 0 := hreg.params.q_ne_zero
  have hq1 : ‖q‖ < 1 := hreg.norm_q_lt_one
  have hv0 : v ≠ 0 := hreg.params.v_ne_zero
  refine addDefectDiff_eq_zero_of_laurentRows_odd_envelope hq0 hq1 hB ha ?_ hv0 (hexp q u v hreg)
  intro n
  have hsp_norm : ‖unitSpectator q n‖ = 1 := norm_unitSpectator hq0 hq1 n
  have hsp_ne1 : unitSpectator q n ≠ 1 := unitSpectator_ne_one hq0 n
  refine master_of_hasSum_qshift_odd_envelope hB (spectatorRows s a (unitSpectator q n))
    (fun N k => norm_spectatorRows_le_env_C1EnvelopeEngine hB ha hsp_norm N k)
    (g := fun q' u' => addDefectDiff q' u' (unitSpectator q n))
    (fun q' w' hq'0 _hw' _hq'w' => addDefectDiff_q_mul_left hq'0) ?_
  intro q' w' hq'0 hlo hhi hwne
  exact hexp q' w' (unitSpectator q n)
    (expansionRegion_of_spectator hq'0 hlo hhi hwne hsp_norm hsp_ne1)

theorem diff_identity_of_rowExpansion_odd_envelope {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hexp : ∀ q' u' v' : K, ExpansionRegion q' u' v' →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M,
            (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k - u'⁻¹ ^ k)) * q' ^ M)
        (addDefectDiff q' u' v'))
    (hreg : ExpansionRegion q u v) :
    (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) :=
  addDefectDiff_eq_zero_iff'.mp
    (addDefectDiff_eq_zero_of_rowExpansion_odd_envelope hB ha hexp hreg)

theorem diff_identity_curve_of_rowExpansion_odd_envelope {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hexp : ∀ q' u' v' : K, ExpansionRegion q' u' v' →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M,
            (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k - u'⁻¹ ^ k)) * q' ^ M)
        (addDefectDiff q' u' v'))
    (hreg : ExpansionRegion q u v) :
    (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      -((pointY q u - (curve q).toAffine.negY (pointX q u) (pointY q u)) *
        (pointY q v - (curve q).toAffine.negY (pointX q v) (pointY q v))) :=
  addDefectDiff_eq_zero_iff_curve.mp
    (addDefectDiff_eq_zero_of_rowExpansion_odd_envelope hB ha hexp hreg)

end EnvD1Conclusions

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows rows_eval_eq_zero_of_master_at_spectators symSumNum symProdNum AddParams addDefectSum addDefectProd addDefectSum_eq_zero_iff addDefectProd_eq_zero_iff addDefectSum_q_mul_left norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma spec_eq_zero_of_master ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMulInt sum_Ico_divisorSum_mul_eq_sum_Sols Fz Gz Gz_neg Fz_mul_Gz xDivTerm_eq_mul_Fz tent tent_one cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice MuTranslation ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section EnvReindexEven

private def shiftPairEv_C1EnvelopeEngineEven : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)

private lemma shiftPairEv_injective_C1EnvelopeEngineEven : Function.Injective shiftPairEv_C1EnvelopeEngineEven := by
  intro p p' h
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := p'
  simp only [shiftPairEv_C1EnvelopeEngineEven, Prod.mk.injEq] at h ⊢
  omega

private lemma mem_range_shiftPairEv_C1EnvelopeEngineEven {p : ℕ × ℕ} (h : p.2 ≤ p.1) :
    p ∈ Set.range shiftPairEv_C1EnvelopeEngineEven :=
  ⟨(p.1 - p.2, p.2), by
    simp only [shiftPairEv_C1EnvelopeEngineEven]
    exact Prod.ext (by omega) rfl⟩

private lemma tsum_prod_eq_tsum_sum_antidiagonalEv_C1EnvelopeEngineEven {f : ℕ × ℕ → K} (hf : Summable f) :
    ∑' p : ℕ × ℕ, f p = ∑' M : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal M, f p := by
  have he := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq f
  rw [← he]
  have hsum : Summable fun x : Σ M : ℕ, (Finset.HasAntidiagonal.antidiagonal M : Finset (ℕ × ℕ)) =>
      f (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd x) := by
    have h1 := (Equiv.summable_iff (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ))).mpr hf
    simpa [Function.comp_def] using h1
  rw [hsum.tsum_sigma]
  refine tsum_congr fun M => ?_
  rw [tsum_fintype, ← Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal M) f]
  exact Finset.sum_congr rfl fun c _ => rfl

private lemma summable_of_shift_bound_factoredEv_C1EnvelopeEngineEven {f : ℕ × ℕ → K} {g h : ℕ → ℝ}
    (hg : Summable g) (hh : Summable h)
    (hg0 : ∀ n, 0 ≤ g n) (hh0 : ∀ n, 0 ≤ h n)
    (hvanish : ∀ p : ℕ × ℕ, ¬ p.2 ≤ p.1 → f p = 0)
    (hbound : ∀ p : ℕ × ℕ, ‖f (shiftPairEv_C1EnvelopeEngineEven p)‖ ≤ g p.1 * h p.2) :
    Summable f := by
  have hgeom : Summable fun p : ℕ × ℕ => g p.1 * h p.2 :=
    hg.mul_of_nonneg hh hg0 hh0
  have hcomp : Summable fun p : ℕ × ℕ => f (shiftPairEv_C1EnvelopeEngineEven p) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound hgeom)
  have hsupport : ∀ x ∉ Set.range shiftPairEv_C1EnvelopeEngineEven, f x = 0 := by
    intro x hx
    refine hvanish x fun hle => hx (mem_range_shiftPairEv_C1EnvelopeEngineEven hle)
  have hcomp' : Summable (f ∘ shiftPairEv_C1EnvelopeEngineEven) := by exact hcomp
  exact (shiftPairEv_injective_C1EnvelopeEngineEven.summable_iff hsupport).mp hcomp'

private lemma norm_neg_two_le_oneEv_C1EnvelopeEngineEven : ‖(-2 : K)‖ ≤ 1 := by
  rw [norm_neg]
  have h3 : ((2 : ℕ) : K) = (2 : K) := by norm_num
  have h4 := norm_natCast_le_one K 2
  rwa [h3] at h4

end EnvReindexEven

section EnvFamiliesEven

variable (c : ℕ → ℕ → K) (w q : K)

private noncomputable def hubTEv_C1EnvelopeEngineEven (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then
    c p.1 p.2 * ((q * w) ^ p.2 + (q * w)⁻¹ ^ p.2 - 2) * q ^ p.1 else 0

private noncomputable def alphaTEv_C1EnvelopeEngineEven (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then c p.1 p.2 * w ^ p.2 * q ^ (p.1 + p.2) else 0

private noncomputable def betaTEv_C1EnvelopeEngineEven (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then c p.1 p.2 * w⁻¹ ^ p.2 * q ^ (p.1 - p.2) else 0

private noncomputable def gammaTEv_C1EnvelopeEngineEven (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then (-2 : K) * c p.1 p.2 * q ^ p.1 else 0

variable {c w q}

private lemma hubTEv_eq_C1EnvelopeEngineEven (hq0 : q ≠ 0) (_hw0 : w ≠ 0) (p : ℕ × ℕ) :
    hubTEv_C1EnvelopeEngineEven c w q p = alphaTEv_C1EnvelopeEngineEven c w q p + betaTEv_C1EnvelopeEngineEven c w q p + gammaTEv_C1EnvelopeEngineEven c q p := by
  simp only [hubTEv_C1EnvelopeEngineEven, alphaTEv_C1EnvelopeEngineEven, betaTEv_C1EnvelopeEngineEven, gammaTEv_C1EnvelopeEngineEven]
  by_cases hg : 1 ≤ p.2 ∧ p.2 ≤ p.1
  · rw [if_pos hg, if_pos hg, if_pos hg, if_pos hg]
    obtain ⟨j, hj⟩ : ∃ j, p.1 = j + p.2 := ⟨p.1 - p.2, by omega⟩
    rw [hj]
    have hsub : j + p.2 - p.2 = j := by omega
    rw [hsub]
    have hqp : q ^ p.2 ≠ 0 := pow_ne_zero _ hq0
    have hcancel : q ^ p.2 * q⁻¹ ^ p.2 = 1 := by
      rw [inv_pow, mul_inv_cancel₀ hqp]
    have hsplit : (q * w)⁻¹ ^ p.2 = q⁻¹ ^ p.2 * w⁻¹ ^ p.2 := by
      rw [mul_inv, mul_pow]
    rw [hsplit]
    linear_combination (c (j + p.2) p.2 * w⁻¹ ^ p.2 * q ^ j) * hcancel
  · rw [if_neg hg, if_neg hg, if_neg hg, if_neg hg]
    ring

variable {B : ℝ} {d : ℕ}

set_option maxHeartbeats 4000000 in
private lemma summable_alphaTEv_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) : Summable (alphaTEv_C1EnvelopeEngineEven c w q) := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hqwpos : (0 : ℝ) < ‖q‖ * ‖w‖ := mul_pos hqpos (lt_trans one_pos hw)
  refine summable_of_shift_bound_factoredEv_C1EnvelopeEngineEven
    (g := fun i => B * ((i : ℝ) + 1) ^ d * ‖q‖ ^ i)
    (h := fun k => ((k : ℝ) + 1) ^ d * (‖q‖ * ‖w‖) ^ k)
    (((summable_polyGeomSeq d hqpos hq1).mul_left B).congr fun i => by ring)
    (summable_polyGeomSeq d hqwpos hqw)
    (fun i => by positivity) (fun k => by positivity) ?_ ?_
  · intro p hp
    simp only [alphaTEv_C1EnvelopeEngineEven]
    exact if_neg fun hg => hp hg.2
  · intro p
    simp only [alphaTEv_C1EnvelopeEngineEven, shiftPairEv_C1EnvelopeEngineEven]
    by_cases hg : 1 ≤ p.2
    · rw [if_pos ⟨hg, by omega⟩]
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖c (p.1 + p.2) p.2‖ ≤ B * (((p.1 : ℝ) + 1) ^ d * ((p.2 : ℝ) + 1) ^ d) :=
        le_trans (hc _ _)
          (mul_le_mul_of_nonneg_left (add_one_pow_le_mul_add_one_pow d p.1 p.2) hB)
      have h2 : ‖q‖ ^ (p.1 + p.2 + p.2) = ‖q‖ ^ p.1 * ‖q‖ ^ p.2 * ‖q‖ ^ p.2 := by
        rw [← pow_add, ← pow_add]
      have h3 : ‖q‖ ^ p.2 ≤ 1 := pow_le_one₀ (norm_nonneg q) (le_of_lt hq1)
      calc ‖c (p.1 + p.2) p.2‖ * ‖w‖ ^ p.2 * ‖q‖ ^ (p.1 + p.2 + p.2)
          = ‖c (p.1 + p.2) p.2‖ * (‖q‖ ^ p.1 * (‖q‖ * ‖w‖) ^ p.2 * ‖q‖ ^ p.2) := by
            rw [h2, mul_pow]
            ring
        _ ≤ (B * (((p.1 : ℝ) + 1) ^ d * ((p.2 : ℝ) + 1) ^ d))
              * (‖q‖ ^ p.1 * (‖q‖ * ‖w‖) ^ p.2 * 1) := by
            refine mul_le_mul h1 ?_ (by positivity) (by positivity)
            refine mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (B * ((p.1 : ℝ) + 1) ^ d * ‖q‖ ^ p.1)
              * (((p.2 : ℝ) + 1) ^ d * (‖q‖ * ‖w‖) ^ p.2) := by ring
    · rw [if_neg fun hcon => hg hcon.1, norm_zero]
      positivity

set_option maxHeartbeats 4000000 in
private lemma summable_betaTEv_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) : Summable (betaTEv_C1EnvelopeEngineEven c w q) := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hw0 : w ≠ 0 := ne_zero_of_one_lt_norm hw
  have hρ : ‖w⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hw
  have hρpos : (0 : ℝ) < ‖w⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hw0)
  refine summable_of_shift_bound_factoredEv_C1EnvelopeEngineEven
    (g := fun i => B * ((i : ℝ) + 1) ^ d * ‖q‖ ^ i)
    (h := fun k => ((k : ℝ) + 1) ^ d * ‖w⁻¹‖ ^ k)
    (((summable_polyGeomSeq d hqpos hq1).mul_left B).congr fun i => by ring)
    (summable_polyGeomSeq d hρpos hρ)
    (fun i => by positivity) (fun k => by positivity) ?_ ?_
  · intro p hp
    simp only [betaTEv_C1EnvelopeEngineEven]
    exact if_neg fun hg => hp hg.2
  · intro p
    simp only [betaTEv_C1EnvelopeEngineEven, shiftPairEv_C1EnvelopeEngineEven]
    by_cases hg : 1 ≤ p.2
    · rw [if_pos ⟨hg, by omega⟩]
      have h0 : p.1 + p.2 - p.2 = p.1 := by omega
      rw [h0, norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖c (p.1 + p.2) p.2‖ ≤ B * (((p.1 : ℝ) + 1) ^ d * ((p.2 : ℝ) + 1) ^ d) :=
        le_trans (hc _ _)
          (mul_le_mul_of_nonneg_left (add_one_pow_le_mul_add_one_pow d p.1 p.2) hB)
      calc ‖c (p.1 + p.2) p.2‖ * ‖w⁻¹‖ ^ p.2 * ‖q‖ ^ p.1
          ≤ (B * (((p.1 : ℝ) + 1) ^ d * ((p.2 : ℝ) + 1) ^ d)) * ‖w⁻¹‖ ^ p.2 * ‖q‖ ^ p.1 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (B * ((p.1 : ℝ) + 1) ^ d * ‖q‖ ^ p.1)
              * (((p.2 : ℝ) + 1) ^ d * ‖w⁻¹‖ ^ p.2) := by ring
    · rw [if_neg fun hcon => hg hcon.1, norm_zero]
      positivity

set_option maxHeartbeats 4000000 in

private lemma summable_gammaTEv_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) : Summable (gammaTEv_C1EnvelopeEngineEven c q) := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  refine summable_of_shift_bound_factoredEv_C1EnvelopeEngineEven
    (g := fun i => B * ((i : ℝ) + 1) ^ d * ‖q‖ ^ i)
    (h := fun k => ((k : ℝ) + 1) ^ d * ‖q‖ ^ k)
    (((summable_polyGeomSeq d hqpos hq1).mul_left B).congr fun i => by ring)
    (summable_polyGeomSeq d hqpos hq1)
    (fun i => by positivity) (fun k => by positivity) ?_ ?_
  · intro p hp
    simp only [gammaTEv_C1EnvelopeEngineEven]
    exact if_neg fun hg => hp hg.2
  · intro p
    simp only [gammaTEv_C1EnvelopeEngineEven, shiftPairEv_C1EnvelopeEngineEven]
    by_cases hg : 1 ≤ p.2
    · rw [if_pos ⟨hg, by omega⟩]
      rw [norm_mul, norm_mul, norm_pow]
      have h1 : ‖c (p.1 + p.2) p.2‖ ≤ B * (((p.1 : ℝ) + 1) ^ d * ((p.2 : ℝ) + 1) ^ d) :=
        le_trans (hc _ _)
          (mul_le_mul_of_nonneg_left (add_one_pow_le_mul_add_one_pow d p.1 p.2) hB)
      have h2 : ‖q‖ ^ (p.1 + p.2) = ‖q‖ ^ p.1 * ‖q‖ ^ p.2 := by rw [← pow_add]
      calc ‖(-2 : K)‖ * ‖c (p.1 + p.2) p.2‖ * ‖q‖ ^ (p.1 + p.2)
          ≤ 1 * (B * (((p.1 : ℝ) + 1) ^ d * ((p.2 : ℝ) + 1) ^ d)) * ‖q‖ ^ (p.1 + p.2) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul norm_neg_two_le_oneEv_C1EnvelopeEngineEven h1 (norm_nonneg _) zero_le_one
        _ = (B * ((p.1 : ℝ) + 1) ^ d * ‖q‖ ^ p.1)
              * (((p.2 : ℝ) + 1) ^ d * ‖q‖ ^ p.2) := by rw [h2]; ring
    · rw [if_neg fun hcon => hg hcon.1, norm_zero]
      positivity

private lemma summable_hubTEv_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) : Summable (hubTEv_C1EnvelopeEngineEven c w q) := by
  have hw0 : w ≠ 0 := ne_zero_of_one_lt_norm hw
  exact (((summable_alphaTEv_C1EnvelopeEngineEven hB hc hq0 hw hqw).add (summable_betaTEv_C1EnvelopeEngineEven hB hc hq0 hw hqw)).add
    (summable_gammaTEv_C1EnvelopeEngineEven hB hc hq0 hw hqw)).congr fun p => (hubTEv_eq_C1EnvelopeEngineEven hq0 hw0 p).symm

end EnvFamiliesEven

section EnvRegroupEven

variable {c : ℕ → ℕ → K} {w q : K} {B : ℝ} {d : ℕ}

set_option maxHeartbeats 4000000 in
private lemma tsum_alphaTEv_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    ∑' p : ℕ × ℕ, alphaTEv_C1EnvelopeEngineEven c w q p = ∑' M : ℕ, specAlpha c w M * q ^ M := by
  rw [tsum_prod_eq_tsum_sum_antidiagonalEv_C1EnvelopeEngineEven (summable_alphaTEv_C1EnvelopeEngineEven hB hc hq0 hw hqw)]
  refine tsum_congr fun M => ?_
  simp only [specAlpha]
  rw [Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpM : p.1 + p.2 = M := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  simp only [alphaTEv_C1EnvelopeEngineEven]
  by_cases hg : 1 ≤ p.2 ∧ p.2 ≤ p.1
  · rw [if_pos hg, if_pos hg, hpM]
  · rw [if_neg hg, if_neg hg, zero_mul]

set_option maxHeartbeats 4000000 in
private lemma tsum_betaTEv_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    ∑' p : ℕ × ℕ, betaTEv_C1EnvelopeEngineEven c w q p = ∑' M : ℕ, specTail c w M * q ^ M := by
  have hsupport : Function.support (betaTEv_C1EnvelopeEngineEven c w q) ⊆ Set.range shiftPairEv_C1EnvelopeEngineEven := by
    intro p hp
    by_contra hcon
    refine hp ?_
    simp only [betaTEv_C1EnvelopeEngineEven]
    refine if_neg fun hg => hcon (mem_range_shiftPairEv_C1EnvelopeEngineEven hg.2)
  rw [← shiftPairEv_injective_C1EnvelopeEngineEven.tsum_eq hsupport]
  have hcomp : Summable fun p : ℕ × ℕ => betaTEv_C1EnvelopeEngineEven c w q (shiftPairEv_C1EnvelopeEngineEven p) :=
    (summable_betaTEv_C1EnvelopeEngineEven hB hc hq0 hw hqw).comp_injective shiftPairEv_injective_C1EnvelopeEngineEven
  rw [hcomp.tsum_prod]
  refine tsum_congr fun M => ?_
  simp only [specTail]
  rw [← tsum_mul_right]
  refine tsum_congr fun k => ?_
  simp only [betaTEv_C1EnvelopeEngineEven, shiftPairEv_C1EnvelopeEngineEven]
  by_cases hk : 1 ≤ k
  · rw [if_pos ⟨hk, by omega⟩, if_pos hk]
    have h0 : M + k - k = M := by omega
    rw [h0]
  · rw [if_neg fun hcon => hk hcon.1, if_neg hk, zero_mul]

set_option maxHeartbeats 4000000 in
private lemma tsum_gammaTEv_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    ∑' p : ℕ × ℕ, gammaTEv_C1EnvelopeEngineEven c q p = ∑' M : ℕ, specGamma c M * q ^ M := by
  rw [(summable_gammaTEv_C1EnvelopeEngineEven hB hc hq0 hw hqw).tsum_prod]
  refine tsum_congr fun N => ?_
  have hvanish : ∀ k ∉ Finset.Icc 1 N, gammaTEv_C1EnvelopeEngineEven c q (N, k) = 0 := by
    intro k hk
    simp only [gammaTEv_C1EnvelopeEngineEven]
    refine if_neg fun hg => hk (Finset.mem_Icc.mpr ⟨hg.1, hg.2⟩)
  rw [tsum_eq_sum hvanish]
  simp only [specGamma]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  simp only [gammaTEv_C1EnvelopeEngineEven]
  rw [if_pos ⟨hk'.1, hk'.2⟩]

set_option maxHeartbeats 4000000 in

private lemma tsum_hubTEv_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    ∑' p : ℕ × ℕ, hubTEv_C1EnvelopeEngineEven c w q p
      = ∑' M : ℕ,
          (∑ k ∈ Finset.Icc 1 M, c M k * ((q * w) ^ k + (q * w)⁻¹ ^ k - 2)) * q ^ M := by
  rw [(summable_hubTEv_C1EnvelopeEngineEven hB hc hq0 hw hqw).tsum_prod]
  refine tsum_congr fun N => ?_
  have hvanish : ∀ k ∉ Finset.Icc 1 N, hubTEv_C1EnvelopeEngineEven c w q (N, k) = 0 := by
    intro k hk
    simp only [hubTEv_C1EnvelopeEngineEven]
    refine if_neg fun hg => hk (Finset.mem_Icc.mpr ⟨hg.1, hg.2⟩)
  rw [tsum_eq_sum hvanish, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  simp only [hubTEv_C1EnvelopeEngineEven]
  rw [if_pos ⟨hk'.1, hk'.2⟩]

end EnvRegroupEven

section EnvSpecBoundsEven

variable {c : ℕ → ℕ → K} {w q : K} {B : ℝ} {d : ℕ}

private lemma norm_specAlpha_le_envEv_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) (hw : 1 ≤ ‖w‖) (M : ℕ) :
    ‖specAlpha c w M‖ ≤ B * ((M : ℝ) + 1) ^ d * ‖w‖ ^ M := by
  refine norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (mul_nonneg hB (by positivity)) (by positivity)) fun p hp => ?_
  have hmem := Finset.mem_filter.mp hp
  have hanti := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem.1
  have hp1M : p.1 ≤ M := by omega
  have hp2M : p.2 ≤ M := by omega
  rw [norm_mul, norm_pow]
  have h1 : ‖c p.1 p.2‖ ≤ B * ((p.1 : ℝ) + 1) ^ d := hc _ _
  have h1' : B * ((p.1 : ℝ) + 1) ^ d ≤ B * ((M : ℝ) + 1) ^ d := by
    refine mul_le_mul_of_nonneg_left ?_ hB
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have : (p.1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hp1M
    linarith
  have h2 : ‖w‖ ^ p.2 ≤ ‖w‖ ^ M := pow_le_pow_right₀ hw hp2M
  calc ‖c p.1 p.2‖ * ‖w‖ ^ p.2
      ≤ (B * ((M : ℝ) + 1) ^ d) * ‖w‖ ^ M := by
        refine mul_le_mul (le_trans h1 h1') h2 (by positivity) ?_
        exact mul_nonneg hB (by positivity)
    _ = B * ((M : ℝ) + 1) ^ d * ‖w‖ ^ M := by ring

private lemma norm_specTail_le_envEv_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hwr : ‖w⁻¹‖ ≤ r) (M : ℕ) :
    ‖specTail c w M‖ ≤ B * ((M : ℝ) + 1) ^ d * polyGeomBound d r := by
  have hC0 : 0 ≤ B * ((M : ℝ) + 1) ^ d * polyGeomBound d r :=
    mul_nonneg (mul_nonneg hB (by positivity)) (polyGeomBound_nonneg d (le_of_lt hr0))
  refine norm_tsum_le_of_forall_le_of_nonneg hC0 fun k => ?_
  by_cases hk : 1 ≤ k
  · rw [if_pos hk, norm_mul, norm_pow]
    have h1 : ‖c (M + k) k‖ ≤ B * (((M : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d) :=
      le_trans (hc _ _)
        (mul_le_mul_of_nonneg_left (add_one_pow_le_mul_add_one_pow d M k) hB)
    have h2 : ‖w⁻¹‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg _) hwr k
    calc ‖c (M + k) k‖ * ‖w⁻¹‖ ^ k
        ≤ (B * (((M : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d)) * r ^ k := by
          refine mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (B * ((M : ℝ) + 1) ^ d) * (((k : ℝ) + 1) ^ d * r ^ k) := by ring
      _ ≤ (B * ((M : ℝ) + 1) ^ d) * polyGeomBound d r := by
          refine mul_le_mul_of_nonneg_left (le_polyGeomBound d hr0 hr1 k) ?_
          exact mul_nonneg hB (by positivity)
      _ = B * ((M : ℝ) + 1) ^ d * polyGeomBound d r := by ring
  · rw [if_neg hk, norm_zero]
    exact hC0

private lemma norm_specGamma_le_env_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) (M : ℕ) :
    ‖specGamma c M‖ ≤ B * ((M : ℝ) + 1) ^ d := by
  refine norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hB (by positivity)) fun k _ => ?_
  rw [norm_mul]
  calc ‖(-2 : K)‖ * ‖c M k‖
      ≤ 1 * ‖c M k‖ := mul_le_mul_of_nonneg_right norm_neg_two_le_oneEv_C1EnvelopeEngineEven (norm_nonneg _)
    _ = ‖c M k‖ := one_mul _
    _ ≤ B * ((M : ℝ) + 1) ^ d := hc M k

private lemma norm_spectatorRows_le_envEv_C1EnvelopeEngineEven {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (hB : 0 ≤ B) (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    {v : K} (hv : ‖v‖ = 1) (M k : ℕ) :
    ‖spectatorRows s a v M k‖ ≤ B * ((M : ℝ) + 1) ^ d :=
  norm_finsetSum_mul_zpow_le_of_norm_eq_one hv
    (mul_nonneg hB (by positivity)) (fun j _ => ha M k j)

private lemma summable_specAlpha_mul_pow_envEv_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    Summable fun M : ℕ => specAlpha c w M * q ^ M := by
  have hqwpos : (0 : ℝ) < ‖q‖ * ‖w‖ :=
    mul_pos (norm_pos_iff.mpr hq0) (lt_trans one_pos hw)
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_)
    ((summable_polyGeomSeq d hqwpos hqw).mul_left B))
  rw [norm_mul, norm_pow]
  have h1 := norm_specAlpha_le_envEv_C1EnvelopeEngineEven hB hc (le_of_lt hw) M
  have h2 : ‖w‖ ^ M * ‖q‖ ^ M = (‖q‖ * ‖w‖) ^ M := by rw [mul_pow]; ring
  calc ‖specAlpha c w M‖ * ‖q‖ ^ M
      ≤ (B * ((M : ℝ) + 1) ^ d * ‖w‖ ^ M) * ‖q‖ ^ M :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = B * (((M : ℝ) + 1) ^ d * (‖q‖ * ‖w‖) ^ M) := by rw [← h2]; ring

private lemma summable_specTail_mul_pow_envEv_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    Summable fun M : ℕ => specTail c w M * q ^ M := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hw0 : w ≠ 0 := ne_zero_of_one_lt_norm hw
  have hρpos : (0 : ℝ) < ‖w⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hw0)
  have hρ : ‖w⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hw
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_)
    ((summable_polyGeomSeq d hqpos hq1).mul_left (B * polyGeomBound d ‖w⁻¹‖)))
  rw [norm_mul, norm_pow]
  have h1 := norm_specTail_le_envEv_C1EnvelopeEngineEven hB hc hρpos hρ le_rfl M
  calc ‖specTail c w M‖ * ‖q‖ ^ M
      ≤ (B * ((M : ℝ) + 1) ^ d * polyGeomBound d ‖w⁻¹‖) * ‖q‖ ^ M :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = B * polyGeomBound d ‖w⁻¹‖ * (((M : ℝ) + 1) ^ d * ‖q‖ ^ M) := by ring

private lemma summable_specGamma_mul_pow_env_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    Summable fun M : ℕ => specGamma c M * q ^ M := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hw hqw
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_)
    ((summable_polyGeomSeq d hqpos hq1).mul_left B))
  rw [norm_mul, norm_pow]
  have h1 := norm_specGamma_le_env_C1EnvelopeEngineEven (c := c) hB hc M
  calc ‖specGamma c M‖ * ‖q‖ ^ M
      ≤ (B * ((M : ℝ) + 1) ^ d) * ‖q‖ ^ M :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = B * (((M : ℝ) + 1) ^ d * ‖q‖ ^ M) := by ring

private lemma summable_spec_series_env_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hq0 : q ≠ 0) (hw : 1 < ‖w‖) (hqw : ‖q‖ * ‖w‖ < 1) :
    Summable fun M : ℕ => (specAlpha c w M + specTail c w M + specGamma c M) * q ^ M := by
  refine (((summable_specAlpha_mul_pow_envEv_C1EnvelopeEngineEven hB hc hq0 hw hqw).add
    (summable_specTail_mul_pow_envEv_C1EnvelopeEngineEven hB hc hq0 hw hqw)).add
    (summable_specGamma_mul_pow_env_C1EnvelopeEngineEven hB hc hq0 hw hqw)).congr fun M => ?_
  ring

end EnvSpecBoundsEven

section EnvAbstractMasterEven

set_option maxHeartbeats 4000000 in

theorem master_of_hasSum_qshift_envelope {B : ℝ} {d : ℕ} (hB : 0 ≤ B) (c : ℕ → ℕ → K)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) {g : K → K → K}
    (hinv : ∀ q w : K, q ≠ 0 → 1 < ‖w‖ → ‖q‖ * ‖w‖ < 1 → g q (q * w) = g q w)
    (hrepr : ∀ q w : K, q ≠ 0 → ‖q‖ < ‖w‖ → ‖q‖ * ‖w‖ < 1 → ‖w‖ ≠ 1 →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)) * q ^ M) (g q w)) :
    ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha c w M + specTail c w M + specGamma c M := by
  intro M w hw
  have hw0 : w ≠ 0 := ne_zero_of_one_lt_norm hw
  have hwpos : (0 : ℝ) < ‖w‖ := lt_trans one_pos hw
  have hwne1 : ‖w‖ ≠ 1 := ne_of_gt hw

  have hq₀0 : w⁻¹ * w⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hw0) (inv_ne_zero hw0)
  have hwinv_lt : ‖w⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hw
  have hwinv_pos : (0 : ℝ) < ‖w⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hw0)
  have hq₀norm : ‖w⁻¹ * w⁻¹‖ = ‖w⁻¹‖ * ‖w⁻¹‖ := norm_mul _ _
  have hq₀1 : ‖w⁻¹ * w⁻¹‖ < 1 := by
    rw [hq₀norm]
    nlinarith

  have hregion : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ → ‖q‖ * ‖w‖ < 1 := by
    intro q hq hqle
    have h1 : ‖w⁻¹‖ * ‖w‖ = 1 := by
      rw [norm_inv]
      field_simp
    have h2 : ‖q‖ ≤ ‖w⁻¹‖ * ‖w⁻¹‖ := by rwa [hq₀norm] at hqle
    nlinarith
  have hqlt_of : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ → ‖q‖ < ‖w‖ := by
    intro q hq hqle
    have h1 : ‖q‖ < 1 := lt_of_le_of_lt hqle hq₀1
    linarith

  have ha : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ →
      Summable fun N => (∑ k ∈ Finset.Icc 1 N, c N k * (w ^ k + w⁻¹ ^ k - 2)) * q ^ N := by
    intro q hq hqle
    exact (hrepr q w hq (hqlt_of q hq hqle) (hregion q hq hqle) hwne1).summable
  have hb : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ →
      Summable fun N => (specAlpha c w N + specTail c w N + specGamma c N) * q ^ N := by
    intro q hq hqle
    exact summable_spec_series_env_C1EnvelopeEngineEven hB hc hq hw (hregion q hq hqle)
  have heq : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖w⁻¹ * w⁻¹‖ →
      ∑' N, (∑ k ∈ Finset.Icc 1 N, c N k * (w ^ k + w⁻¹ ^ k - 2)) * q ^ N
        = ∑' N, (specAlpha c w N + specTail c w N + specGamma c N) * q ^ N := by
    intro q hq hqle
    have hqw : ‖q‖ * ‖w‖ < 1 := hregion q hq hqle
    have hq1 : ‖q‖ < 1 := lt_of_le_of_lt hqle hq₀1
    have hqlt : ‖q‖ < ‖w‖ := hqlt_of q hq hqle
    have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq

    have hqw_norm : ‖q * w‖ = ‖q‖ * ‖w‖ := norm_mul q w
    have hqw_lt1 : ‖q * w‖ < 1 := by rw [hqw_norm]; exact hqw
    have hqw_gt : ‖q‖ < ‖q * w‖ := by
      rw [hqw_norm]
      nlinarith [mul_pos hqpos (sub_pos.mpr hw)]
    have hq_qw : ‖q‖ * ‖q * w‖ < 1 := by
      rw [hqw_norm]
      have h := mul_lt_mul_of_pos_left hqw hqpos
      rw [mul_one] at h
      linarith
    have hqw_ne1 : ‖q * w‖ ≠ 1 := ne_of_lt hqw_lt1

    have hX := hrepr q w hq hqlt hqw hwne1
    have hXq := hrepr q (q * w) hq hqw_gt hq_qw hqw_ne1

    have hSα := summable_specAlpha_mul_pow_envEv_C1EnvelopeEngineEven hB hc hq hw hqw
    have hSτ := summable_specTail_mul_pow_envEv_C1EnvelopeEngineEven hB hc hq hw hqw
    have hSγ := summable_specGamma_mul_pow_env_C1EnvelopeEngineEven hB hc hq hw hqw

    calc ∑' N, (∑ k ∈ Finset.Icc 1 N, c N k * (w ^ k + w⁻¹ ^ k - 2)) * q ^ N
        = g q w := hX.tsum_eq
      _ = g q (q * w) := (hinv q w hq hw hqw).symm
      _ = ∑' N, (∑ k ∈ Finset.Icc 1 N, c N k * ((q * w) ^ k + (q * w)⁻¹ ^ k - 2)) * q ^ N :=
          hXq.tsum_eq.symm
      _ = ∑' p : ℕ × ℕ, hubTEv_C1EnvelopeEngineEven c w q p := (tsum_hubTEv_C1EnvelopeEngineEven hB hc hq hw hqw).symm
      _ = ∑' p : ℕ × ℕ, (alphaTEv_C1EnvelopeEngineEven c w q p + betaTEv_C1EnvelopeEngineEven c w q p + gammaTEv_C1EnvelopeEngineEven c q p) :=
          tsum_congr fun p => hubTEv_eq_C1EnvelopeEngineEven hq hw0 p
      _ = (∑' p : ℕ × ℕ, (alphaTEv_C1EnvelopeEngineEven c w q p + betaTEv_C1EnvelopeEngineEven c w q p)) + ∑' p : ℕ × ℕ, gammaTEv_C1EnvelopeEngineEven c q p :=
          ((summable_alphaTEv_C1EnvelopeEngineEven hB hc hq hw hqw).add (summable_betaTEv_C1EnvelopeEngineEven hB hc hq hw hqw)).tsum_add
            (summable_gammaTEv_C1EnvelopeEngineEven hB hc hq hw hqw)
      _ = ((∑' p : ℕ × ℕ, alphaTEv_C1EnvelopeEngineEven c w q p) + ∑' p : ℕ × ℕ, betaTEv_C1EnvelopeEngineEven c w q p)
            + ∑' p : ℕ × ℕ, gammaTEv_C1EnvelopeEngineEven c q p := by
          rw [(summable_alphaTEv_C1EnvelopeEngineEven hB hc hq hw hqw).tsum_add (summable_betaTEv_C1EnvelopeEngineEven hB hc hq hw hqw)]
      _ = ((∑' M, specAlpha c w M * q ^ M) + ∑' M, specTail c w M * q ^ M)
            + ∑' M, specGamma c M * q ^ M := by
          rw [tsum_alphaTEv_C1EnvelopeEngineEven hB hc hq hw hqw, tsum_betaTEv_C1EnvelopeEngineEven hB hc hq hw hqw,
            tsum_gammaTEv_C1EnvelopeEngineEven hB hc hq hw hqw]
      _ = (∑' M, (specAlpha c w M * q ^ M + specTail c w M * q ^ M))
            + ∑' M, specGamma c M * q ^ M := by
          rw [hSα.tsum_add hSτ]
      _ = ∑' M, ((specAlpha c w M * q ^ M + specTail c w M * q ^ M)
            + specGamma c M * q ^ M) := by
          rw [(hSα.add hSτ).tsum_add hSγ]
      _ = ∑' N, (specAlpha c w N + specTail c w N + specGamma c N) * q ^ N :=
          tsum_congr fun N => by ring

  have hε : (0 : ℝ) < ‖w⁻¹ * w⁻¹‖ := norm_pos_iff.mpr hq₀0
  refine coeff_eq_of_hasSum_eq
    (A := fun N => ∑ k ∈ Finset.Icc 1 N, c N k * (w ^ k + w⁻¹ ^ k - 2))
    (Bc := fun N => specAlpha c w N + specTail c w N + specGamma c N)
    hε (fun q' hq'0 hq'lt => ?_) M
  have hq'le : ‖q'‖ ≤ ‖w⁻¹ * w⁻¹‖ := le_of_lt hq'lt
  refine ⟨g q' w, hrepr q' w hq'0 (hqlt_of q' hq'0 hq'le) (hregion q' hq'0 hq'le) hwne1, ?_⟩
  have h1 : (∑' N, (specAlpha c w N + specTail c w N + specGamma c N) * q' ^ N) = g q' w := by
    rw [← heq q' hq'0 hq'le,
      (hrepr q' w hq'0 (hqlt_of q' hq'0 hq'le) (hregion q' hq'0 hq'le) hwne1).tsum_eq]
  exact h1 ▸ (hb q' hq'0 hq'le).hasSum

end EnvAbstractMasterEven

section EnvBoundedDescentEven

variable {c : ℕ → ℕ → K} {B : ℝ} {d : ℕ}

set_option maxHeartbeats 4000000 in

private lemma spec_eq_zero_of_diamond_env_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) {M k₀ : ℕ}
    (hk₀1 : 1 ≤ k₀) (hk₀M : k₀ ≤ M)
    (hdiamond : ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k) = specTail c w M)
    (hbig : ∀ k', k₀ < k' → k' ≤ M → c M k' = 0) :
    c M k₀ = 0 := by

  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
  have hx0 : x ≠ 0 := ne_zero_of_one_lt_norm hx
  have hxinv : ‖x⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hx
  have hxinv_pos : (0 : ℝ) < ‖x⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hx0)
  set v : ℕ → K := fun t => x ^ (t + 1) with hv
  have hv0 : ∀ t, v t ≠ 0 := fun t => pow_ne_zero _ hx0
  have hvnorm : ∀ t, ‖v t‖ = ‖x‖ ^ (t + 1) := fun t => by rw [hv]; exact norm_pow x (t + 1)
  have hvbig : ∀ t, 1 < ‖v t‖ := by
    intro t
    rw [hvnorm t]
    exact one_lt_pow₀ hx (Nat.succ_ne_zero t)
  have hvinvnorm : ∀ t, ‖(v t)⁻¹‖ = ‖x⁻¹‖ ^ (t + 1) := by
    intro t
    rw [norm_inv, hvnorm t, norm_inv, inv_pow]
  have hvinvle : ∀ t, ‖(v t)⁻¹‖ ≤ ‖x⁻¹‖ := by
    intro t
    rw [hvinvnorm t]
    calc ‖x⁻¹‖ ^ (t + 1) = ‖x⁻¹‖ ^ t * ‖x⁻¹‖ := pow_succ _ _
      _ ≤ 1 * ‖x⁻¹‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact pow_le_one₀ (norm_nonneg _) (le_of_lt hxinv)
      _ = ‖x⁻¹‖ := one_mul _

  set Cst : ℝ := B * ((M : ℝ) + 1) ^ d * polyGeomBound d ‖x⁻¹‖ with hCst

  set f : ℕ → K := fun t => specTail c (v t) M * (v t)⁻¹ ^ k₀ with hf

  have hf0 : Tendsto f atTop (nhds 0) := by
    have hbound : ∀ t, ‖f t‖ ≤ Cst * (‖x⁻¹‖ ^ k₀) ^ (t + 1) := by
      intro t
      rw [hf]
      simp only []
      rw [norm_mul, norm_pow]
      have h1 : ‖specTail c (v t) M‖ ≤ Cst := by
        rw [hCst]
        exact norm_specTail_le_envEv_C1EnvelopeEngineEven hB hc hxinv_pos hxinv (hvinvle t) M
      have h2 : ‖(v t)⁻¹‖ ^ k₀ = (‖x⁻¹‖ ^ (t + 1)) ^ k₀ := by rw [hvinvnorm t]
      have h3 : (‖x⁻¹‖ ^ (t + 1)) ^ k₀ = (‖x⁻¹‖ ^ k₀) ^ (t + 1) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have h4 : (0 : ℝ) ≤ ‖(v t)⁻¹‖ ^ k₀ := pow_nonneg (norm_nonneg _) _
      calc ‖specTail c (v t) M‖ * ‖(v t)⁻¹‖ ^ k₀ ≤ Cst * ‖(v t)⁻¹‖ ^ k₀ :=
            mul_le_mul_of_nonneg_right h1 h4
        _ = Cst * (‖x⁻¹‖ ^ k₀) ^ (t + 1) := by rw [h2, h3]
    have hratio : ‖x⁻¹‖ ^ k₀ < 1 :=
      pow_lt_one₀ (norm_nonneg _) hxinv (by omega)
    have hgeo : Tendsto (fun t : ℕ => Cst * (‖x⁻¹‖ ^ k₀) ^ (t + 1)) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => (‖x⁻¹‖ ^ k₀) ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg (norm_nonneg _) _) hratio
      have h2 : Tendsto (fun t : ℕ => (‖x⁻¹‖ ^ k₀) ^ (t + 1)) atTop (nhds 0) :=
        h1.comp (tendsto_add_atTop_nat 1)
      have h3 := h2.const_mul Cst
      simpa using h3
    exact squeeze_zero_norm hbound hgeo

  have hflim : Tendsto f atTop (nhds (c M k₀)) := by
    have hfeq : ∀ t, f t
        = ∑ k ∈ Finset.Icc 1 M, c M k * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀ := by
      intro t
      rw [hf]
      simp only []
      rw [← hdiamond (v t) (hvbig t), Finset.sum_mul]
    have hterm : ∀ k ∈ Finset.Icc 1 M,
        Tendsto (fun t => c M k * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀)
          atTop (nhds (if k = k₀ then c M k₀ else 0)) := by
      intro k hk
      have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hpt : ∀ t, c M k * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀
          = c M k * ((x ^ k * (x ^ k₀)⁻¹) ^ (t + 1) + ((x ^ (k + k₀))⁻¹) ^ (t + 1)) := by
        intro t
        rw [hv]
        simp only []
        have hxp : x ^ (t + 1) ≠ 0 := pow_ne_zero _ hx0
        field_simp
        ring
      rcases lt_trichotomy k k₀ with hlt | heq | hgt
      · rw [if_neg (Nat.ne_of_lt hlt)]
        have hw1 : ‖x ^ k * (x ^ k₀)⁻¹‖ < 1 := by
          rw [norm_mul, norm_inv, norm_pow, norm_pow, ← div_eq_mul_inv]
          rw [div_lt_one (pow_pos (lt_trans one_pos hx) k₀)]
          exact pow_lt_pow_right₀ hx hlt
        have hz : ‖(x ^ (k + k₀))⁻¹‖ < 1 := by
          rw [norm_inv, inv_lt_one_iff₀]
          right
          rw [norm_pow]
          exact one_lt_pow₀ hx (by omega)
        have hwlim : Tendsto (fun t : ℕ => (x ^ k * (x ^ k₀)⁻¹) ^ (t + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hw1).comp (tendsto_add_atTop_nat 1)
        have hzlim : Tendsto (fun t : ℕ => ((x ^ (k + k₀))⁻¹) ^ (t + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz).comp (tendsto_add_atTop_nat 1)
        have hlim : Tendsto (fun t => c M k
            * ((x ^ k * (x ^ k₀)⁻¹) ^ (t + 1) + ((x ^ (k + k₀))⁻¹) ^ (t + 1)))
            atTop (nhds (c M k * (0 + 0))) :=
          (hwlim.add hzlim).const_mul _
        rw [add_zero, mul_zero] at hlim
        refine Tendsto.congr (fun t => (hpt t).symm) hlim
      · subst heq
        rw [if_pos rfl]
        have hw1 : x ^ k * (x ^ k)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hx0)
        have hz : ‖(x ^ (k + k))⁻¹‖ < 1 := by
          rw [norm_inv, inv_lt_one_iff₀]
          right
          rw [norm_pow]
          exact one_lt_pow₀ hx (by omega)
        have hzlim : Tendsto (fun t : ℕ => ((x ^ (k + k))⁻¹) ^ (t + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz).comp (tendsto_add_atTop_nat 1)
        have hlim : Tendsto (fun t => c M k
            * ((x ^ k * (x ^ k)⁻¹) ^ (t + 1) + ((x ^ (k + k))⁻¹) ^ (t + 1)))
            atTop (nhds (c M k * (1 + 0))) := by
          have h1 : Tendsto (fun t : ℕ => (x ^ k * (x ^ k)⁻¹) ^ (t + 1)) atTop (nhds 1) := by
            simp only [hw1, one_pow]
            exact tendsto_const_nhds
          exact (h1.add hzlim).const_mul _
        rw [add_zero, mul_one] at hlim
        refine Tendsto.congr (fun t => (hpt t).symm) hlim
      · rw [if_neg (by omega)]
        have hzero : c M k = 0 := hbig k hgt hkM
        have hconst : ∀ t, c M k * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀ = 0 := by
          intro t
          rw [hzero]
          simp
        refine Tendsto.congr (fun t => (hconst t).symm) tendsto_const_nhds
    have hsum : Tendsto (fun t => ∑ k ∈ Finset.Icc 1 M,
        c M k * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀)
        atTop (nhds (∑ k ∈ Finset.Icc 1 M, if k = k₀ then c M k₀ else 0)) :=
      tendsto_finsetSum _ hterm
    have hcollapse : (∑ k ∈ Finset.Icc 1 M, if k = k₀ then c M k₀ else 0) = c M k₀ := by
      rw [Finset.sum_ite_eq' (Finset.Icc 1 M) k₀ (fun _ => c M k₀)]
      rw [if_pos (Finset.mem_Icc.mpr ⟨hk₀1, hk₀M⟩)]
    rw [hcollapse] at hsum
    exact Tendsto.congr (fun t => (hfeq t).symm) hsum
  exact tendsto_nhds_unique hflim hf0

private lemma spec_row_eq_zero_of_diamond_env_C1EnvelopeEngineEven (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) {M : ℕ}
    (hdiamond : ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k) = specTail c w M) :
    ∀ k, 1 ≤ k → k ≤ M → c M k = 0 := by
  have hcol : ∀ e j : ℕ, 1 ≤ j → j ≤ M → M ≤ j + e → c M j = 0 := by
    intro e
    induction e with
    | zero =>
        intro j h1 h2 hd
        have hjM : j = M := by omega
        subst hjM
        exact spec_eq_zero_of_diamond_env_C1EnvelopeEngineEven hB hc h1 le_rfl hdiamond
          (fun k' hk' hk'' => absurd hk'' (by omega))
    | succ e ihd =>
        intro j h1 h2 hd
        rcases (by omega : M ≤ j + e ∨ j + e < M) with h | h
        · exact ihd j h1 h2 h
        · refine spec_eq_zero_of_diamond_env_C1EnvelopeEngineEven hB hc h1 h2 hdiamond fun k' hk' hk'' => ?_
          exact ihd k' (by omega) hk'' (by omega)
  intro k h1 h2
  exact hcol M k h1 h2 (by omega)

theorem spec_eq_zero_of_master_envelope (hB : 0 ≤ B)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hmaster : ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha c w M + specTail c w M + specGamma c M) :
    ∀ N k : ℕ, 1 ≤ k → k ≤ N → c N k = 0 := by
  suffices h : ∀ R N k : ℕ, N ≤ R → 1 ≤ k → k ≤ N → c N k = 0 by
    intro N k h1 h2
    exact h N N k le_rfl h1 h2
  intro R
  induction R with
  | zero =>
      intro N k hNR h1 h2
      omega
  | succ R ihR =>
      intro N k hNR h1 h2
      rcases Nat.lt_or_ge N (R + 1) with hN | hN
      · exact ihR N k (by omega) h1 h2
      have hNeq : N = R + 1 := by omega

      have hdiamond : ∀ w : K, 1 < ‖w‖ →
          ∑ j ∈ Finset.Icc 1 N, c N j * (w ^ j + w⁻¹ ^ j) = specTail c w N := by
        intro w hw
        have h1' := hmaster N w hw

        have hα : specAlpha c w N = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have hmem := Finset.mem_filter.mp hp
          have hanti := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem.1
          have hp1 : 1 ≤ p.2 := hmem.2.1
          have hp2 : p.2 ≤ p.1 := hmem.2.2
          have hlow : c p.1 p.2 = 0 := by
            refine ihR p.1 p.2 (by omega) hp1 hp2
          rw [hlow]
          simp
        rw [hα, zero_add] at h1'

        calc ∑ j ∈ Finset.Icc 1 N, c N j * (w ^ j + w⁻¹ ^ j)
            = ∑ j ∈ Finset.Icc 1 N,
                (c N j * (w ^ j + w⁻¹ ^ j - 2) + (2 : K) * c N j) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
          _ = (∑ j ∈ Finset.Icc 1 N, c N j * (w ^ j + w⁻¹ ^ j - 2))
                + ∑ j ∈ Finset.Icc 1 N, (2 : K) * c N j :=
              Finset.sum_add_distrib
          _ = (specTail c w N + specGamma c N)
                + ∑ j ∈ Finset.Icc 1 N, (2 : K) * c N j := by
              rw [h1']
          _ = specTail c w N
                + (∑ j ∈ Finset.Icc 1 N, (-2 : K) * c N j
                    + ∑ j ∈ Finset.Icc 1 N, (2 : K) * c N j) := by
              rw [specGamma, add_assoc]
          _ = specTail c w N := by
              rw [← Finset.sum_add_distrib]
              have hzero : ∑ j ∈ Finset.Icc 1 N, ((-2 : K) * c N j + (2 : K) * c N j) = 0 := by
                refine Finset.sum_eq_zero fun j _ => ?_
                ring
              rw [hzero, add_zero]
      exact spec_row_eq_zero_of_diamond_env_C1EnvelopeEngineEven hB hc hdiamond k h1 h2

end EnvBoundedDescentEven

section EnvEngineWiringEven

theorem eq_zero_of_master_rows_envelope {B : ℝ} {d : ℕ} {c : ℕ → ℕ → K} {q u g : K}
    (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hmaster : ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha c w M + specTail c w M + specGamma c M)
    (hrepr : HasSum (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M) g) :
    g = 0 := by
  have hzero := spec_eq_zero_of_master_envelope hB hc hmaster
  have hfun : (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M) = fun _ => 0 := by
    funext M
    have hsum0 : ∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k + u⁻¹ ^ k - 2) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' := Finset.mem_Icc.mp hk
      rw [hzero M k hk'.1 hk'.2, zero_mul]
    rw [hsum0, zero_mul]
  rw [hfun] at hrepr
  exact hrepr.unique hasSum_zero

end EnvEngineWiringEven

section EnvSpectatorUpgradeEven

variable {q : K}

theorem rows_eval_eq_zero_of_master_at_spectators_envelope
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hmaster : ∀ n : ℕ, ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M,
          spectatorRows s a (unitSpectator q n) M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha (spectatorRows s a (unitSpectator q n)) w M
          + specTail (spectatorRows s a (unitSpectator q n)) w M
          + specGamma (spectatorRows s a (unitSpectator q n)) M) :
    ∀ M k : ℕ, 1 ≤ k → k ≤ M → ∀ v : K, v ≠ 0 → ∑ j ∈ s M k, a M k j * v ^ j = 0 := by
  intro M k hk1 hkM
  have hvan : ∀ n : ℕ, ∑ j ∈ s M k, a M k j * (unitSpectator q n) ^ j = 0 := by
    intro n
    have hbound : ∀ N k', ‖spectatorRows s a (unitSpectator q n) N k'‖
        ≤ B * ((N : ℝ) + 1) ^ d :=
      fun N k' => norm_spectatorRows_le_envEv_C1EnvelopeEngineEven hB ha (norm_unitSpectator hq0 hq n) N k'
    exact spec_eq_zero_of_master_envelope hB hbound (hmaster n) M k hk1 hkM
  refine laurent_eval_eq_zero_of_infinite_roots
    (Set.infinite_range_of_injective (unitSpectator_injective hq0 hq)) ?_ ?_
  · rintro v ⟨n, rfl⟩
    exact unitSpectator_ne_zero hq0 hq n
  · rintro v ⟨n, rfl⟩
    exact hvan n

end EnvSpectatorUpgradeEven

section EnvConclusionsEven

variable {q u v : K}

theorem symAdd_sum_of_rows_envelope {B : ℝ} {d : ℕ} {c : ℕ → ℕ → K}
    (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d)
    (hmaster : ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha c w M + specTail c w M + specGamma c M)
    (hrepr : HasSum (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, c M k * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M) (addDefectSum q u v)) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) :=
  addDefectSum_eq_zero_iff.mp (eq_zero_of_master_rows_envelope hB hc hmaster hrepr)

private lemma laurentRows_repr_eq_zero_env_C1EnvelopeEngineEven {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (hzero : ∀ M k : ℕ, 1 ≤ k → k ≤ M → ∀ v : K, v ≠ 0 →
      ∑ j ∈ s M k, a M k j * v ^ j = 0)
    (hv0 : v ≠ 0) :
    (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v ^ j) * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M)
      = fun _ => 0 := by
  funext M
  have hsum0 : ∑ k ∈ Finset.Icc 1 M,
      (∑ j ∈ s M k, a M k j * v ^ j) * (u ^ k + u⁻¹ ^ k - 2) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' := Finset.mem_Icc.mp hk
    rw [hzero M k hk'.1 hk'.2 v hv0, zero_mul]
  rw [hsum0, zero_mul]

theorem symAdd_sum_of_laurentRows_envelope (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hmaster : ∀ n : ℕ, ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M,
          spectatorRows s a (unitSpectator q n) M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha (spectatorRows s a (unitSpectator q n)) w M
          + specTail (spectatorRows s a (unitSpectator q n)) w M
          + specGamma (spectatorRows s a (unitSpectator q n)) M)
    (hv0 : v ≠ 0)
    (hrepr : HasSum (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v ^ j) * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M)
      (addDefectSum q u v)) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) := by
  have hzero := rows_eval_eq_zero_of_master_at_spectators_envelope hq0 hq hB ha hmaster
  rw [laurentRows_repr_eq_zero_env_C1EnvelopeEngineEven hzero hv0] at hrepr
  exact addDefectSum_eq_zero_iff.mp (hrepr.unique hasSum_zero)

theorem symAdd_prod_of_laurentRows_envelope (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hmaster : ∀ n : ℕ, ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M,
          spectatorRows s a (unitSpectator q n) M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha (spectatorRows s a (unitSpectator q n)) w M
          + specTail (spectatorRows s a (unitSpectator q n)) w M
          + specGamma (spectatorRows s a (unitSpectator q n)) M)
    (hv0 : v ≠ 0)
    (hrepr : HasSum (fun M : ℕ =>
      (∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v ^ j) * (u ^ k + u⁻¹ ^ k - 2)) * q ^ M)
      (addDefectProd q u v)) :
    pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
      symProdNum q (pointX q u) (pointX q v) := by
  have hzero := rows_eval_eq_zero_of_master_at_spectators_envelope hq0 hq hB ha hmaster
  rw [laurentRows_repr_eq_zero_env_C1EnvelopeEngineEven hzero hv0] at hrepr
  exact addDefectProd_eq_zero_iff.mp (hrepr.unique hasSum_zero)

set_option maxHeartbeats 4000000 in

theorem symAdd_sum_of_rowExpansion_envelope {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hexp : ∀ q' u' v' : K, ExpansionRegion q' u' v' →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M,
            (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)) * q' ^ M)
        (addDefectSum q' u' v'))
    (hreg : ExpansionRegion q u v) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) := by
  have hq0 : q ≠ 0 := hreg.params.q_ne_zero
  have hq1 : ‖q‖ < 1 := hreg.norm_q_lt_one
  have hv0 : v ≠ 0 := hreg.params.v_ne_zero
  refine symAdd_sum_of_laurentRows_envelope hq0 hq1 hB ha ?_ hv0 (hexp q u v hreg)

  intro n
  have hsp_norm : ‖unitSpectator q n‖ = 1 := norm_unitSpectator hq0 hq1 n
  have hsp_ne1 : unitSpectator q n ≠ 1 := unitSpectator_ne_one hq0 n
  refine master_of_hasSum_qshift_envelope hB (spectatorRows s a (unitSpectator q n))
    (fun N k => norm_spectatorRows_le_envEv_C1EnvelopeEngineEven hB ha hsp_norm N k)
    (g := fun q' u' => addDefectSum q' u' (unitSpectator q n))
    (fun q' w' hq'0 _hw' _hq'w' => addDefectSum_q_mul_left hq'0) ?_
  intro q' w' hq'0 hlo hhi hwne
  exact hexp q' w' (unitSpectator q n)
    (expansionRegion_of_spectator hq'0 hlo hhi hwne hsp_norm hsp_ne1)

theorem symAdd_sum_of_coeff_eq_envelope {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hrow : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      addDefectSumCoeff u' v' M
        = ∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2))
    (hreg : ExpansionRegion q u v) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) :=
  symAdd_sum_of_rowExpansion_envelope hB ha (rowExpansion_of_coeff_eq hrow) hreg

end EnvConclusionsEven

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows rows_eval_eq_zero_of_master_at_spectators symSumNum symProdNum AddParams addDefectSum addDefectProd addDefectSum_eq_zero_iff addDefectProd_eq_zero_iff addDefectSum_q_mul_left norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma spec_eq_zero_of_master ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMulInt sum_Ico_divisorSum_mul_eq_sum_Sols Fz Gz Gz_neg Fz_mul_Gz xDivTerm_eq_mul_Fz tent tent_one cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice MuTranslation ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

open FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section RowForms

theorem sum_Ico_Gz_one_mul_tent_eq_sum (w : K) (hw0 : w ≠ 0) (e : ℕ) :
    ∑ m ∈ Finset.Ico 1 e, (Gz w 1 * tent w m)
      = ∑ j ∈ Finset.Ico 1 e, (2 * ((e : K) - (j : K)) - 1) * Gz w (j : ℤ) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    have h1e : (1 : ℕ) ≤ e := he
    rw [Finset.sum_Ico_succ_top h1e, Finset.sum_Ico_succ_top h1e, ih,
      Gz_one_mul_tent_eq_sum w hw0 e]
    have hcoeff : ∑ j ∈ Finset.Ico 1 e, (2 * ((e : K) - (j : K)) - 1) * Gz w (j : ℤ)
          + 2 * ∑ j ∈ Finset.Ico 1 e, Gz w (j : ℤ)
        = ∑ j ∈ Finset.Ico 1 e, (2 * (((e + 1 : ℕ) : K) - (j : K)) - 1) * Gz w (j : ℤ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    push_cast at hcoeff ⊢
    linear_combination hcoeff

private theorem sum_Ico_mul_Gz_one_mul_tent_eq_sum_aux_C1DiffCancellation (w : K) (hw0 : w ≠ 0) (e : ℕ) :
    ∑ m ∈ Finset.Ico 1 e, ((e : K) - (m : K)) * (Gz w 1 * tent w m)
      = ∑ j ∈ Finset.Ico 1 e, ((e : K) - (j : K)) ^ 2 * Gz w (j : ℤ) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    have h1e : (1 : ℕ) ≤ e := he
    rw [Finset.sum_Ico_succ_top h1e, Finset.sum_Ico_succ_top h1e]
    have hdistrib : ∑ m ∈ Finset.Ico 1 e, (((e + 1 : ℕ) : K) - (m : K)) * (Gz w 1 * tent w m)
        = ∑ m ∈ Finset.Ico 1 e, ((e : K) - (m : K)) * (Gz w 1 * tent w m)
          + ∑ m ∈ Finset.Ico 1 e, (Gz w 1 * tent w m) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by push_cast; ring
    have hdistrib' : ∑ j ∈ Finset.Ico 1 e, (((e + 1 : ℕ) : K) - (j : K)) ^ 2 * Gz w (j : ℤ)
        = ∑ j ∈ Finset.Ico 1 e, ((e : K) - (j : K)) ^ 2 * Gz w (j : ℤ)
          + ∑ j ∈ Finset.Ico 1 e, (2 * ((e : K) - (j : K)) - 1) * Gz w (j : ℤ)
          + 2 * ∑ j ∈ Finset.Ico 1 e, Gz w (j : ℤ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    have hrun := sum_Ico_Gz_one_mul_tent_eq_sum w hw0 e
    have hG := Gz_one_mul_tent_eq_sum w hw0 e
    push_cast at hdistrib hdistrib' ih hrun hG ⊢
    linear_combination hdistrib + ih + hrun + hG - hdistrib'

theorem sum_Ico_mul_Gz_one_mul_tent_eq_sum (w : K) (hw0 : w ≠ 0) (e : ℕ) :
    ∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz w 1 * tent w m)
      = ∑ j ∈ Finset.Ico 1 e, ((e : K) - (j : K)) ^ 2 * Gz w (j : ℤ) := by
  calc ∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz w 1 * tent w m)
      = ∑ m ∈ Finset.Ico 1 e, ((e : K) - (m : K)) * (Gz w 1 * tent w m) :=
        Finset.sum_congr rfl fun m hm => by
          rw [Nat.cast_sub (le_of_lt (Finset.mem_Ico.1 hm).2)]
    _ = ∑ j ∈ Finset.Ico 1 e, ((e : K) - (j : K)) ^ 2 * Gz w (j : ℤ) :=
        sum_Ico_mul_Gz_one_mul_tent_eq_sum_aux_C1DiffCancellation w hw0 e

theorem Gz_one_mul_telescope_eq_sum (w : K) (hw0 : w ≠ 0) (d : ℕ) :
    Gz w 1 * ∑ j ∈ Finset.range (d / 2), tent w (d - 1 - 2 * j)
      = ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * Gz w (i : ℤ) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
      · simp
      · simp
    · obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
      have IH := ih m (by omega)

      have hsplit : ∑ j ∈ Finset.range ((m + 2) / 2), tent w (m + 2 - 1 - 2 * j)
          = (∑ j ∈ Finset.range (m / 2), tent w (m - 1 - 2 * j)) + tent w (m + 1) := by
        have h2 : (m + 2) / 2 = m / 2 + 1 := by omega
        rw [h2, Finset.sum_range_succ']
        congr 1
        exact Finset.sum_congr rfl fun j _ => by congr 1; omega
      rw [hsplit, mul_add]
      have htent := Gz_one_mul_tent_eq_sum w hw0 (m + 1)
      rcases Nat.eq_zero_or_pos m with rfl | hm
      ·
        simp only [Nat.zero_div, Finset.range_zero, Finset.sum_empty, mul_zero, zero_add]
        rw [show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton, tent_one hw0, mul_one]
        push_cast
        ring
      ·
        have hpeel2 : ∑ i ∈ Finset.Ico 1 (m + 2), (((m + 2 : ℕ) : K) - (i : K)) * Gz w (i : ℤ)
            = ∑ i ∈ Finset.Ico 1 (m + 1), (((m + 2 : ℕ) : K) - (i : K)) * Gz w (i : ℤ)
              + (((m + 2 : ℕ) : K) - ((m + 1 : ℕ) : K)) * Gz w ((m + 1 : ℕ) : ℤ) :=
          Finset.sum_Ico_succ_top (by omega) _
        have hpeel1 : ∑ i ∈ Finset.Ico 1 (m + 1), (((m + 2 : ℕ) : K) - (i : K)) * Gz w (i : ℤ)
            = ∑ i ∈ Finset.Ico 1 m, (((m + 2 : ℕ) : K) - (i : K)) * Gz w (i : ℤ)
              + (((m + 2 : ℕ) : K) - ((m : ℕ) : K)) * Gz w ((m : ℕ) : ℤ) :=
          Finset.sum_Ico_succ_top (by omega) _
        have hpeelG : ∑ j ∈ Finset.Ico 1 (m + 1), Gz w (j : ℤ)
            = ∑ j ∈ Finset.Ico 1 m, Gz w (j : ℤ) + Gz w ((m : ℕ) : ℤ) :=
          Finset.sum_Ico_succ_top (by omega) _
        have hcomb : ∑ i ∈ Finset.Ico 1 m, (((m + 2 : ℕ) : K) - (i : K)) * Gz w (i : ℤ)
            = ∑ i ∈ Finset.Ico 1 m, ((m : K) - (i : K)) * Gz w (i : ℤ)
              + 2 * ∑ i ∈ Finset.Ico 1 m, Gz w (i : ℤ) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by push_cast; ring
        push_cast at IH htent hpeel2 hpeel1 hpeelG hcomb ⊢
        linear_combination IH + htent - hpeel2 - hpeel1 + 2 * hpeelG - hcomb

end RowForms

section Cancellation

private noncomputable def phiOdd_C1DiffCancellation (v : K) : ℤ → K := fun n => (n : K) * Gz v n

private theorem phiOdd_apply_C1DiffCancellation (v : K) (n : ℤ) : phiOdd_C1DiffCancellation v n = (n : K) * Gz v n := rfl

private theorem phiOdd_zero_C1DiffCancellation (v : K) : phiOdd_C1DiffCancellation v 0 = 0 := by
  simp [phiOdd_C1DiffCancellation]

private theorem phiOdd_neg_C1DiffCancellation (v : K) (a : ℤ) : phiOdd_C1DiffCancellation v (-a) = phiOdd_C1DiffCancellation v a := by
  simp only [phiOdd_C1DiffCancellation, Int.cast_neg, Gz_neg]
  ring

theorem svCancellation (hv0 : v ≠ 0) (M : ℕ) :
    12 * ∑ e ∈ M.divisors, (e : K) *
        ∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz v 1 * tent v m)
      + ∑ d ∈ M.divisors, (d : K) * ((d : K) ^ 3 - (d : K)) * Gz v (d : ℤ)
    = 12 * ∑ d ∈ M.divisors, (d : K) ^ 2 *
          (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))
      + 12 * ∑ a ∈ Finset.Ico 1 M,
          (∑ e ∈ a.divisors, (e : K) ^ 2 * Gz v (e : ℤ))
            * ∑ f ∈ (M - a).divisors, (f : K) * Fz v (f : ℤ) := by
  classical

  have hTA : ∑ e ∈ M.divisors, (e : K) *
        ∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz v 1 * tent v m)
      = ∑ e ∈ M.divisors, (e : K) *
          ∑ j ∈ Finset.Ico 1 e, ((e : K) - (j : K)) ^ 2 * Gz v (j : ℤ) :=
    Finset.sum_congr rfl fun e _ => by rw [sum_Ico_mul_Gz_one_mul_tent_eq_sum v hv0 e]
  have hTB : ∑ d ∈ M.divisors, (d : K) ^ 2 *
        (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))
      = ∑ d ∈ M.divisors, (d : K) ^ 2 *
          ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * Gz v (i : ℤ) :=
    Finset.sum_congr rfl fun d _ => by rw [Gz_one_mul_telescope_eq_sum v hv0 d]

  have hconv : ∑ a ∈ Finset.Ico 1 M,
        (∑ e ∈ a.divisors, (e : K) ^ 2 * Gz v (e : ℤ))
          * ∑ f ∈ (M - a).divisors, (f : K) * Fz v (f : ℤ)
      = ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) *
          (Gz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + Gz v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
            - 2 * Gz v (x.1 : ℤ)) := by
    rw [sum_Ico_divisorSum_mul_eq_sum_Sols (R := K)
      (fun e => (e : K) ^ 2 * Gz v (e : ℤ)) (fun f => (f : K) * Fz v (f : ℤ)) M]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hprod := Fz_mul_Gz (u := v) hv0 (x.2.2.1 : ℤ) (x.1 : ℤ)
    have hflip : Gz v ((x.2.2.1 : ℤ) - (x.1 : ℤ)) = -Gz v ((x.1 : ℤ) - (x.2.2.1 : ℤ)) := by
      rw [show (x.2.2.1 : ℤ) - (x.1 : ℤ) = -((x.1 : ℤ) - (x.2.2.1 : ℤ)) by ring, Gz_neg]
    have hcomm : ((x.2.2.1 : ℤ) + (x.1 : ℤ)) = ((x.1 : ℤ) + (x.2.2.1 : ℤ)) := by ring
    rw [hcomm, hflip] at hprod
    calc ((x.1 : K) ^ 2 * Gz v (x.1 : ℤ)) * ((x.2.2.1 : K) * Fz v (x.2.2.1 : ℤ))
        = (x.1 : K) ^ 2 * (x.2.2.1 : K) * (Fz v (x.2.2.1 : ℤ) * Gz v (x.1 : ℤ)) := by ring
      _ = _ := by rw [hprod]; ring

  have hswap_add : ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) ^ 2 *
        Gz v ((x.1 : ℤ) + (x.2.2.1 : ℤ))
      = ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) * Gz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) := by
    rw [sum_swap₁_total M (fun x => (x.1 : K) * (x.2.2.1 : K) ^ 2 *
      Gz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [swap₁]
    rw [show (x.2.2.1 : ℤ) + (x.1 : ℤ) = (x.1 : ℤ) + (x.2.2.1 : ℤ) by ring]
    ring
  have hswap_sub : ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) ^ 2 *
        Gz v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
      = ∑ x ∈ Sols M, -((x.1 : K) ^ 2 * (x.2.2.1 : K) * Gz v ((x.1 : ℤ) - (x.2.2.1 : ℤ))) := by
    rw [sum_swap₁_total M (fun x => (x.1 : K) * (x.2.2.1 : K) ^ 2 *
      Gz v ((x.1 : ℤ) - (x.2.2.1 : ℤ)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [swap₁]
    rw [show (x.2.2.1 : ℤ) - (x.1 : ℤ) = -((x.1 : ℤ) - (x.2.2.1 : ℤ)) by ring, Gz_neg]
    ring
  have hswap_c : ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) ^ 2 * Gz v (x.2.2.1 : ℤ)
      = ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) * Gz v (x.1 : ℤ) := by
    rw [sum_swap₁_total M (fun x => (x.1 : K) * (x.2.2.1 : K) ^ 2 * Gz v (x.2.2.1 : ℤ))]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [swap₁]
    ring
  have hneg : ∑ x ∈ Sols M, -((x.1 : K) ^ 2 * (x.2.2.1 : K) * Gz v ((x.1 : ℤ) - (x.2.2.1 : ℤ)))
      = -∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) * Gz v ((x.1 : ℤ) - (x.2.2.1 : ℤ)) := by
    rw [← Finset.sum_neg_distrib]

  have hphi := phi_general (A := K) (phiOdd_C1DiffCancellation v) (phiOdd_zero_C1DiffCancellation v) (phiOdd_neg_C1DiffCancellation v) M

  have hE5 : ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) *
        (phiOdd_C1DiffCancellation v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + phiOdd_C1DiffCancellation v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
          - 2 * phiOdd_C1DiffCancellation v (x.1 : ℤ) - 2 * phiOdd_C1DiffCancellation v (x.2.2.1 : ℤ))
      = ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * phiOdd_C1DiffCancellation v ((x.1 : ℤ) + (x.2.2.1 : ℤ))
        + ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * phiOdd_C1DiffCancellation v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
        - 2 * ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * phiOdd_C1DiffCancellation v (x.1 : ℤ)
        - 2 * ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * phiOdd_C1DiffCancellation v (x.2.2.1 : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hE1split : ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) *
        phiOdd_C1DiffCancellation v ((x.1 : ℤ) + (x.2.2.1 : ℤ))
      = ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) * Gz v ((x.1 : ℤ) + (x.2.2.1 : ℤ))
        + ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) ^ 2 * Gz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [phiOdd_apply_C1DiffCancellation]
    push_cast
    ring
  have hE1 : ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * phiOdd_C1DiffCancellation v ((x.1 : ℤ) + (x.2.2.1 : ℤ))
      = 2 * ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) *
          Gz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) := by
    rw [hE1split, hswap_add]; ring
  have hE2split : ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) *
        phiOdd_C1DiffCancellation v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
      = ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) * Gz v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
        - ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) ^ 2 * Gz v ((x.1 : ℤ) - (x.2.2.1 : ℤ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [phiOdd_apply_C1DiffCancellation]
    push_cast
    ring
  have hE2 : ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * phiOdd_C1DiffCancellation v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
      = 2 * ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) *
          Gz v ((x.1 : ℤ) - (x.2.2.1 : ℤ)) := by
    rw [hE2split, hswap_sub, hneg]; ring
  have hE3 : ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * phiOdd_C1DiffCancellation v (x.1 : ℤ)
      = ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) * Gz v (x.1 : ℤ) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [phiOdd_apply_C1DiffCancellation]
    push_cast
    ring
  have hE4split : ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * phiOdd_C1DiffCancellation v (x.2.2.1 : ℤ)
      = ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) ^ 2 * Gz v (x.2.2.1 : ℤ) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [phiOdd_apply_C1DiffCancellation]
    push_cast
    ring
  have hE4 : ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * phiOdd_C1DiffCancellation v (x.2.2.1 : ℤ)
      = ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) * Gz v (x.1 : ℤ) := by
    rw [hE4split, hswap_c]

  have hval : ∑ δ ∈ M.divisors, ((δ : K) ^ 3 - (δ : K)) * phiOdd_C1DiffCancellation v (δ : ℤ)
      = ∑ d ∈ M.divisors, (d : K) * ((d : K) ^ 3 - (d : K)) * Gz v (d : ℤ) := by
    refine Finset.sum_congr rfl fun δ _ => ?_
    simp only [phiOdd_apply_C1DiffCancellation]
    push_cast
    ring
  have hrow : ∑ δ ∈ M.divisors, ∑ k ∈ Finset.Ico 1 δ,
        (δ : K) * ((δ : K) - (k : K)) * phiOdd_C1DiffCancellation v (k : ℤ)
      = ∑ d ∈ M.divisors, (d : K) ^ 2 *
            ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * Gz v (i : ℤ)
        - ∑ d ∈ M.divisors, (d : K) *
            ∑ j ∈ Finset.Ico 1 d, ((d : K) - (j : K)) ^ 2 * Gz v (j : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [phiOdd_apply_C1DiffCancellation]
    push_cast
    ring

  rw [hE5, hE1, hE2, hE3, hE4, hval, hrow] at hphi

  have hSS : ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) *
        (Gz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + Gz v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
          - 2 * Gz v (x.1 : ℤ))
      = ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) * Gz v ((x.1 : ℤ) + (x.2.2.1 : ℤ))
        + ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) * Gz v ((x.1 : ℤ) - (x.2.2.1 : ℤ))
        - 2 * ∑ x ∈ Sols M, (x.1 : K) ^ 2 * (x.2.2.1 : K) * Gz v (x.1 : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hTA, hTB, hconv, hSS]
  linear_combination -hphi

end Cancellation

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "eq_zero_of_master_rows unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows rows_eval_eq_zero_of_master_at_spectators symSumNum symProdNum AddParams addDefectSum addDefectProd addDefectSum_eq_zero_iff addDefectProd_eq_zero_iff addDefectSum_q_mul_left norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma spec_eq_zero_of_master ne_zero_of_one_lt_norm norm_q_lt_one_of_qshift norm_inv_lt_one_of_one_lt_norm cauchyMulInt sum_Ico_divisorSum_mul_eq_sum_Sols Fz Gz Gz_neg Fz_mul_Gz xDivTerm_eq_mul_Fz tent tent_one cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice MuTranslation ks17_A_exports ks17_B_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section ValueIdentities

theorem two_mul_sum_Ico_id_cast (d : ℕ) :
    (2 : K) * ∑ i ∈ Finset.Ico 1 d, (i : K) = (d : K) ^ 2 - (d : K) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ d), mul_add]
      push_cast
      push_cast at ih
      linear_combination ih

theorem six_mul_sum_Ico_mul_cast (d : ℕ) :
    (6 : K) * ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (i : K) = (d : K) ^ 3 - (d : K) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hgauss := two_mul_sum_Ico_id_cast (K := K) d
      have hsplit : ∑ i ∈ Finset.Ico 1 (d + 1), (((d + 1 : ℕ) : K) - (i : K)) * (i : K)
          = ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (i : K)
            + ∑ i ∈ Finset.Ico 1 d, (i : K) + (d : K) := by
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ d), ← Finset.sum_add_distrib]
        congr 1
        · refine Finset.sum_congr rfl fun i _ => ?_
          push_cast
          ring
        · push_cast
          ring
      push_cast at hsplit ih hgauss ⊢
      linear_combination 6 * hsplit + ih + 3 * hgauss

end ValueIdentities

section CarrierReduction

theorem xCoeff_eq_divisorSum_Fz (w : K) (n : ℕ) :
    xCoeff w n = ∑ f ∈ n.divisors, (f : K) * Fz w (f : ℤ) := by
  rw [xCoeff]
  exact Finset.sum_congr rfl fun f _ => xDivTerm_eq_mul_Fz w f

theorem xfunG1_mul_telescope (hu0 : u ≠ 0) (hu1 : u ≠ 1) (d : ℕ) :
    (xfun u * Gz u 1) * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)
      = (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (i : K)) * (xfun u * Gz u 1)
        + ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K))
            * (Gz u 1 * ∑ j ∈ Finset.range (i / 2), tent u (i - 1 - 2 * j)) := by
  calc (xfun u * Gz u 1) * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)
      = xfun u * (Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)) := by ring
    _ = xfun u * ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * Gz u (i : ℤ) := by
        rw [Gz_one_mul_telescope_eq_sum u hu0 d]
    _ = ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (xfun u * Gz u (i : ℤ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i ∈ Finset.Ico 1 d,
          (((d : K) - (i : K)) * (i : K) * (xfun u * Gz u 1)
            + ((d : K) - (i : K))
                * (Gz u 1 * ∑ j ∈ Finset.range (i / 2), tent u (i - 1 - 2 * j))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [xfun_mul_Gz_split hu0 hu1 i]
        ring
    _ = (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (i : K)) * (xfun u * Gz u 1)
        + ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K))
            * (Gz u 1 * ∑ j ∈ Finset.range (i / 2), tent u (i - 1 - 2 * j)) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]

end CarrierReduction

section CarrierMultiplier

theorem svCarrierMultiplier_eq_zero [CharZero K] (hv0 : v ≠ 0) (M : ℕ) :
    (∑ e ∈ M.divisors, 2 * (e : K)
          * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz v 1 * tent v m)))
      - (∑ d ∈ M.divisors, 2 * (d : K) ^ 2
          * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)))
      + (∑ d ∈ M.divisors, (d : K) * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (i : K))
          * Gz v (d : ℤ))
      - (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, 2 * (d : K) ^ 2 * Gz v (d : ℤ))
          * xCoeff v (M - a))
    = 0 := by
  have hsv := svCancellation hv0 M

  have hA6 : (6 : K) * ∑ e ∈ M.divisors, 2 * (e : K)
        * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz v 1 * tent v m))
      = 12 * ∑ e ∈ M.divisors, (e : K)
          * ∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz v 1 * tent v m) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hB6 : (6 : K) * ∑ d ∈ M.divisors, 2 * (d : K) ^ 2
        * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))
      = 12 * ∑ d ∈ M.divisors, (d : K) ^ 2
          * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hO6 : (6 : K) * ∑ d ∈ M.divisors, (d : K)
        * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (i : K)) * Gz v (d : ℤ)
      = ∑ d ∈ M.divisors, (d : K) * ((d : K) ^ 3 - (d : K)) * Gz v (d : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hval := six_mul_sum_Ico_mul_cast (K := K) d
    linear_combination ((d : K) * Gz v (d : ℤ)) * hval
  have hM6 : (6 : K) * ∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, 2 * (d : K) ^ 2 * Gz v (d : ℤ))
        * xCoeff v (M - a)
      = 12 * ∑ a ∈ Finset.Ico 1 M, (∑ e ∈ a.divisors, (e : K) ^ 2 * Gz v (e : ℤ))
          * ∑ f ∈ (M - a).divisors, (f : K) * Fz v (f : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : (∑ d ∈ a.divisors, 2 * (d : K) ^ 2 * Gz v (d : ℤ))
        = 2 * ∑ e ∈ a.divisors, (e : K) ^ 2 * Gz v (e : ℤ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [h1, xCoeff_eq_divisorSum_Fz]
    ring

  have h6 : (6 : K)
      * ((∑ e ∈ M.divisors, 2 * (e : K)
              * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz v 1 * tent v m)))
          - (∑ d ∈ M.divisors, 2 * (d : K) ^ 2
              * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)))
          + (∑ d ∈ M.divisors, (d : K) * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (i : K))
              * Gz v (d : ℤ))
          - (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, 2 * (d : K) ^ 2 * Gz v (d : ℤ))
              * xCoeff v (M - a)))
      = 0 := by
    linear_combination hA6 - hB6 + hO6 - hM6 + hsv
  exact (mul_eq_zero.mp h6).resolve_left (by norm_num)

end CarrierMultiplier

section BlockDecompositions

private theorem svBlockB2_eq_C1DiffTable [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (M : ℕ) :
    2 * ((xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M)))
      = (∑ e ∈ M.divisors, 2 * (e : K) ^ 3)
            * ((xfun u * Gz u 1) * (xfun v * Gz v 1))
        + (xfun u * Gz u 1)
            * (∑ e ∈ M.divisors, 2 * (e : K)
                * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz v 1 * tent v m)))
        + (xfun v * Gz v 1)
            * (∑ e ∈ M.divisors, 2 * (e : K)
                * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz u 1 * tent u m)))
        + ∑ e ∈ M.divisors, 2 * (e : K)
            * (∑ i ∈ Finset.range e,
                ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j))
                    * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j))
                  - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2),
                        tent u (e - 1 - i - 1 - 2 * j))
                    * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j)))) := by
  rw [xCoeff_sub_xCoeff_eq_divisorSum u v M, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [show (∑ e ∈ M.divisors,
        2 * ((xfun (u * v) - xfun (u * v⁻¹))
          * ((xfun u - xfun v) * ((e : K) * (Fz u (e : ℤ) - Fz v (e : ℤ))))))
      = ∑ e ∈ M.divisors,
          (2 * (e : K) ^ 3 * ((xfun u * Gz u 1) * (xfun v * Gz v 1))
            + (xfun u * Gz u 1)
                * (2 * (e : K)
                    * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz v 1 * tent v m)))
            + (xfun v * Gz v 1)
                * (2 * (e : K)
                    * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz u 1 * tent u m)))
            + 2 * (e : K)
                * (∑ i ∈ Finset.range e,
                    ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j))
                        * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2),
                            tent v (e - i - 1 - 2 * j))
                      - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2),
                            tent u (e - 1 - i - 1 - 2 * j))
                        * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j)))))
      from ?_]
  · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
  · refine Finset.sum_congr rfl fun e _ => ?_
    have hcs := xfun_sub_mul_xfun_sub_mul_Fz_sub_eq_carrier_split hu0 hv0 hu1 hv1 huvm huvd e
    calc 2 * ((xfun (u * v) - xfun (u * v⁻¹))
          * ((xfun u - xfun v) * ((e : K) * (Fz u (e : ℤ) - Fz v (e : ℤ)))))
        = 2 * (e : K) * ((xfun (u * v) - xfun (u * v⁻¹))
            * ((xfun u - xfun v) * (Fz u (e : ℤ) - Fz v (e : ℤ)))) := by ring
      _ = _ := by rw [hcs]; ring

private theorem svBlockCross_eq_C1DiffTable (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ) :
    2 * (xfun u * xfun v) * (∑ d ∈ M.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
      = (∑ d ∈ M.divisors, 2 * (d : K) ^ 3)
            * ((xfun u * Gz u 1) * (xfun v * Gz v 1))
        + (xfun u * Gz u 1)
            * (∑ d ∈ M.divisors, 2 * (d : K) ^ 2
                * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)))
        + (xfun v * Gz v 1)
            * (∑ d ∈ M.divisors, 2 * (d : K) ^ 2
                * (Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)))
        + ∑ d ∈ M.divisors, 2 * (d : K)
            * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
                * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))) := by
  rw [Finset.mul_sum]
  rw [show (∑ d ∈ M.divisors,
        2 * (xfun u * xfun v) * ((d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))))
      = ∑ d ∈ M.divisors,
          (2 * (d : K) ^ 3 * ((xfun u * Gz u 1) * (xfun v * Gz v 1))
            + (xfun u * Gz u 1)
                * (2 * (d : K) ^ 2
                    * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)))
            + (xfun v * Gz v 1)
                * (2 * (d : K) ^ 2
                    * (Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)))
            + 2 * (d : K)
                * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
                    * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))))
      from ?_]
  · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
  · refine Finset.sum_congr rfl fun d _ => ?_
    have hsu := xfun_mul_Gz_split hu0 hu1 d
    have hsv := xfun_mul_Gz_split hv0 hv1 d
    calc 2 * (xfun u * xfun v) * ((d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
        = 2 * (d : K) * ((xfun u * Gz u (d : ℤ)) * (xfun v * Gz v (d : ℤ))) := by ring
      _ = _ := by rw [hsu, hsv]; ring

private theorem svBlockOrderThree_eq_C1DiffTable (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ) :
    (∑ d ∈ M.divisors, (d : K)
        * (Gz v (d : ℤ)
              * ((xfun u * Gz u 1) * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
          + Gz u (d : ℤ)
              * ((xfun v * Gz v 1) * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))))
      = (xfun u * Gz u 1)
            * (∑ d ∈ M.divisors, (d : K)
                * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (i : K)) * Gz v (d : ℤ))
        + (xfun v * Gz v 1)
            * (∑ d ∈ M.divisors, (d : K)
                * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (i : K)) * Gz u (d : ℤ))
        + ∑ d ∈ M.divisors, (d : K)
            * (Gz v (d : ℤ)
                  * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K))
                      * (Gz u 1 * ∑ j ∈ Finset.range (i / 2), tent u (i - 1 - 2 * j)))
              + Gz u (d : ℤ)
                  * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K))
                      * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j)))) := by
  rw [show (∑ d ∈ M.divisors, (d : K)
        * (Gz v (d : ℤ)
              * ((xfun u * Gz u 1) * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
          + Gz u (d : ℤ)
              * ((xfun v * Gz v 1) * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))))
      = ∑ d ∈ M.divisors,
          ((xfun u * Gz u 1)
              * ((d : K) * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (i : K))
                  * Gz v (d : ℤ))
            + (xfun v * Gz v 1)
                * ((d : K) * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (i : K))
                    * Gz u (d : ℤ))
            + (d : K)
                * (Gz v (d : ℤ)
                      * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K))
                          * (Gz u 1 * ∑ j ∈ Finset.range (i / 2), tent u (i - 1 - 2 * j)))
                  + Gz u (d : ℤ)
                      * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K))
                          * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j)))))
      from ?_]
  · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  · refine Finset.sum_congr rfl fun d _ => ?_
    have hu' := xfunG1_mul_telescope hu0 hu1 d
    have hv' := xfunG1_mul_telescope hv0 hv1 d
    linear_combination ((d : K) * Gz v (d : ℤ)) * hu' + ((d : K) * Gz u (d : ℤ)) * hv'

private theorem svBlockMixed_eq_C1DiffTable (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ) :
    (∑ a ∈ Finset.Ico 1 M,
        (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
          * (2 * (xfun u * xCoeff v (M - a) + xfun v * xCoeff u (M - a))))
      = (xfun u * Gz u 1)
            * (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, 2 * (d : K) ^ 2 * Gz v (d : ℤ))
                * xCoeff v (M - a))
        + (xfun v * Gz v 1)
            * (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, 2 * (d : K) ^ 2 * Gz u (d : ℤ))
                * xCoeff u (M - a))
        + ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, 2 * (d : K)
            * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
                  * (Gz v (d : ℤ) * xCoeff v (M - a))
              + (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))
                  * (Gz u (d : ℤ) * xCoeff u (M - a))) := by
  rw [show (∑ a ∈ Finset.Ico 1 M,
        (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
          * (2 * (xfun u * xCoeff v (M - a) + xfun v * xCoeff u (M - a))))
      = ∑ a ∈ Finset.Ico 1 M,
          ((xfun u * Gz u 1)
              * ((∑ d ∈ a.divisors, 2 * (d : K) ^ 2 * Gz v (d : ℤ)) * xCoeff v (M - a))
            + (xfun v * Gz v 1)
                * ((∑ d ∈ a.divisors, 2 * (d : K) ^ 2 * Gz u (d : ℤ)) * xCoeff u (M - a))
            + ∑ d ∈ a.divisors, 2 * (d : K)
                * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
                      * (Gz v (d : ℤ) * xCoeff v (M - a))
                  + (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))
                      * (Gz u (d : ℤ) * xCoeff u (M - a))))
      from ?_]
  · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_

    have hX1u : (xfun u * Gz u 1)
          * ((∑ d ∈ a.divisors, 2 * (d : K) ^ 2 * Gz v (d : ℤ)) * xCoeff v (M - a))
        = ∑ d ∈ a.divisors, (xfun u * Gz u 1)
            * (2 * (d : K) ^ 2 * Gz v (d : ℤ) * xCoeff v (M - a)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
    have hX1v : (xfun v * Gz v 1)
          * ((∑ d ∈ a.divisors, 2 * (d : K) ^ 2 * Gz u (d : ℤ)) * xCoeff u (M - a))
        = ∑ d ∈ a.divisors, (xfun v * Gz v 1)
            * (2 * (d : K) ^ 2 * Gz u (d : ℤ) * xCoeff u (M - a)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_mul, hX1u, hX1v, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hsu := xfun_mul_Gz_split hu0 hu1 d
    have hsv := xfun_mul_Gz_split hv0 hv1 d
    calc (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))
          * (2 * (xfun u * xCoeff v (M - a) + xfun v * xCoeff u (M - a)))
        = 2 * (d : K) * ((xfun u * Gz u (d : ℤ)) * (Gz v (d : ℤ) * xCoeff v (M - a)))
          + 2 * (d : K) * ((xfun v * Gz v (d : ℤ)) * (Gz u (d : ℤ) * xCoeff u (M - a))) := by
          ring
      _ = _ := by rw [hsu, hsv]; ring

end BlockDecompositions

section Assembly

theorem svComplex_eq_rowBlocks [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M) :
    svComplex u v M
      = (∑ e ∈ M.divisors, 2 * (e : K)
            * (∑ i ∈ Finset.range e,
                ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j))
                    * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j))
                  - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2),
                        tent u (e - 1 - i - 1 - 2 * j))
                    * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j)))))
        - (∑ d ∈ M.divisors, 2 * (d : K)
            * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
                * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))))
        + (∑ d ∈ M.divisors, (d : K)
            * (Gz v (d : ℤ)
                  * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K))
                      * (Gz u 1 * ∑ j ∈ Finset.range (i / 2), tent u (i - 1 - 2 * j)))
              + Gz u (d : ℤ)
                  * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K))
                      * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j)))))
        + (∑ a ∈ Finset.Ico 1 M,
            (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
              * (2 * ∑ f ∈ (M - a).divisors, (f : K) * (tent u f + tent v f)))
        - ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, 2 * (d : K)
            * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
                  * (Gz v (d : ℤ) * xCoeff v (M - a))
              + (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))
                  * (Gz u (d : ℤ) * xCoeff u (M - a))) := by
  have hSP := svComplex_eq_simplePoleForm hu0 hu1 hv0 hv1 hM
  have hA := svBlockB2_eq_C1DiffTable hu0 hu1 hv0 hv1 huvm huvd M
  have hB := svBlockCross_eq_C1DiffTable hu0 hu1 hv0 hv1 M
  have hC := svBlockOrderThree_eq_C1DiffTable hu0 hu1 hv0 hv1 M
  have hD := svBlockMixed_eq_C1DiffTable hu0 hu1 hv0 hv1 M
  have hEv := svCarrierMultiplier_eq_zero (v := v) hv0 M
  have hEu := svCarrierMultiplier_eq_zero (v := u) hu0 M
  linear_combination hSP + hA - hB + hC - hD
    + (xfun u * Gz u 1) * hEv + (xfun v * Gz v 1) * hEu

end Assembly

end TateCurve

theorem solution :

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hexp : ∀ q' u' v' : K, ExpansionRegion q' u' v' →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M,
            (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k - u'⁻¹ ^ k)) * q' ^ M)
        (addDefectDiff q' u' v'))
    (hreg : ExpansionRegion q u v),
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (w : K) (hw0 : w ≠ 0) (d : ℕ),
      Gz w 1 * ∑ j ∈ Finset.range (d / 2), tent w (d - 1 - 2 * j) = ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * Gz w (i : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (w : K) (n : ℕ),
      xCoeff w n = ∑ f ∈ n.divisors, (f : K) * Fz w (f : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M),
      svComplex u v M = (∑ e ∈ M.divisors, 2 * (e : K) * (∑ i ∈ Finset.range e, ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j)) - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2), tent u (e - 1 - i - 1 - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j))))) - (∑ d ∈ M.divisors, 2 * (d : K) * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)))) + (∑ d ∈ M.divisors, (d : K) * (Gz v (d : ℤ) * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (Gz u 1 * ∑ j ∈ Finset.range (i / 2), tent u (i - 1 - 2 * j))) + Gz u (d : ℤ) * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j))))) + (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (2 * ∑ f ∈ (M - a).divisors, (f : K) * (tent u f + tent v f))) - ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, 2 * (d : K) * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)) * (Gz v (d : ℤ) * xCoeff v (M - a)) + (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)) * (Gz u (d : ℤ) * xCoeff u (M - a)))) ∧

    (∀ (d : ℕ) {r : ℝ} (h0 : 0 < r) (h1 : r < 1),
      Summable fun k : ℕ => ((k : ℝ) + 1) ^ d * r ^ k) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hmaster : ∀ n : ℕ, ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M,
          spectatorRows s a (unitSpectator q n) M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha (spectatorRows s a (unitSpectator q n)) w M
          + specTail (spectatorRows s a (unitSpectator q n)) w M
          + specGamma (spectatorRows s a (unitSpectator q n)) M),
      ∀ M k : ℕ, 1 ≤ k → k ≤ M → ∀ v : K, v ≠ 0 → ∑ j ∈ s M k, a M k j * v ^ j = 0) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {B : ℝ} {d : ℕ} (hB : 0 ≤ B) (c : ℕ → ℕ → K)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) {g : K → K → K}
    (hinv : ∀ q w : K, q ≠ 0 → 1 < ‖w‖ → ‖q‖ * ‖w‖ < 1 → g q (q * w) = g q w)
    (hrepr : ∀ q w : K, q ≠ 0 → ‖q‖ < ‖w‖ → ‖q‖ * ‖w‖ < 1 → ‖w‖ ≠ 1 →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)) * q ^ M) (g q w)),
      ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ → ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2) = specAlpha c w M + specTail c w M + specGamma c M) :=
  ⟨TateCurve.diff_identity_of_rowExpansion_odd_envelope,
   TateCurve.Gz_one_mul_telescope_eq_sum,
   TateCurve.xCoeff_eq_divisorSum_Fz,
   TateCurve.svComplex_eq_rowBlocks,
   TateCurve.summable_polyGeomSeq,
   TateCurve.rows_eval_eq_zero_of_master_at_spectators_envelope,
   TateCurve.master_of_hasSum_qshift_envelope⟩

end S_TateCurve_ks17_C1_exports
end P2MW
export P2MW.S_TateCurve_ks17_C1_exports (solution)
