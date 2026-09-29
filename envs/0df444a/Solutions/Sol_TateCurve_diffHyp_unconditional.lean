-- Prove2me | solution 1 for TateCurve.diffHyp_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ae586ecc-fe94-533d-bc05-74e06db9ba28

import Mathlib
import Definitions.Def_TateCurve_XMultDistinctRouteB
import Definitions.Def_TateCurve_KeystoneVocab
import Theorems.Thm_TateCurve_ks17_A_exports
import Theorems.Thm_TateCurve_ks17_B_exports
import Theorems.Thm_TateCurve_ks17_C1_exports
import Theorems.Thm_TateCurve_ks17_C3_exports
import Theorems.Thm_TateCurve_ks17_D2_exports
import Theorems.Thm_TateCurve_symAdd_sum_regional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_diffHyp_unconditional

set_option linter.unusedSectionVars false

open scoped NNReal
p2m_open "TateCurve P2MW.S_TateCurve_diffHyp_unconditional.TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset"

universe u_1 u_2
namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum specTail specAlpha specGamma cauchyMulInt Fz Gz Gz_neg Gz_natCast Fz_mul_Gz tent tent_eq_sq_add_sum_Ico sum_mul_Fz_eq_sum_lines_nat cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice unitSpectator spectatorRows ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C3_exports ks17_D2_exports symAdd_sum_regional"
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

namespace AddParams p2m_export "TateCurve.AddParams" "v_ne_zero u_ne_zero offLattice_v offLattice_div offLattice_u offLattice_mul" end AddParams
p2m_open_scoped "TateCurve.AddParams" in
theorem AddParams.latticeRep : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} {u' v' : K} (hp : AddParams q u v)
    (hu' : LatticeRep q u u') (hv' : LatticeRep q v v'),
      AddParams q u' v' :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end TateCurve

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum specTail specAlpha specGamma cauchyMulInt Fz Gz Gz_neg Gz_natCast Fz_mul_Gz tent tent_eq_sq_add_sum_Ico sum_mul_Fz_eq_sum_lines_nat cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice unitSpectator spectatorRows ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C3_exports ks17_D2_exports symAdd_sum_regional"
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
p2m_export "TateCurve" "symSumNum AddParams addDefectSum specTail specAlpha specGamma cauchyMulInt Fz Gz Gz_neg Gz_natCast Fz_mul_Gz tent tent_eq_sq_add_sum_Ico sum_mul_Fz_eq_sum_lines_nat cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice unitSpectator spectatorRows ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C3_exports ks17_D2_exports symAdd_sum_regional"
p2m_open "TateCurve"

theorem diff_identity_of_rowExpansion_odd_envelope : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hexp : ∀ q' u' v' : K, ExpansionRegion q' u' v' →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M,
            (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k - u'⁻¹ ^ k)) * q' ^ M)
        (addDefectDiff q' u' v'))
    (hreg : ExpansionRegion q u v),
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) :=
  TateCurve.ks17_C1_exports.{u_1}.1

theorem Gz_one_mul_telescope_eq_sum : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (w : K) (hw0 : w ≠ 0) (d : ℕ),
      Gz w 1 * ∑ j ∈ Finset.range (d / 2), tent w (d - 1 - 2 * j) = ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * Gz w (i : ℤ) :=
  TateCurve.ks17_C1_exports.{u_1}.2.1

theorem xCoeff_eq_divisorSum_Fz : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (w : K) (n : ℕ),
      xCoeff w n = ∑ f ∈ n.divisors, (f : K) * Fz w (f : ℤ) :=
  TateCurve.ks17_C1_exports.{u_1}.2.2.1

theorem svComplex_eq_rowBlocks : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M),
      svComplex u v M = (∑ e ∈ M.divisors, 2 * (e : K) * (∑ i ∈ Finset.range e, ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j)) - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2), tent u (e - 1 - i - 1 - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j))))) - (∑ d ∈ M.divisors, 2 * (d : K) * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)))) + (∑ d ∈ M.divisors, (d : K) * (Gz v (d : ℤ) * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (Gz u 1 * ∑ j ∈ Finset.range (i / 2), tent u (i - 1 - 2 * j))) + Gz u (d : ℤ) * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j))))) + (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (2 * ∑ f ∈ (M - a).divisors, (f : K) * (tent u f + tent v f))) - ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, 2 * (d : K) * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)) * (Gz v (d : ℤ) * xCoeff v (M - a)) + (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)) * (Gz u (d : ℤ) * xCoeff u (M - a))) :=
  TateCurve.ks17_C1_exports.{u_1}.2.2.2.1

theorem summable_polyGeomSeq : ∀ (d : ℕ) {r : ℝ} (h0 : 0 < r) (h1 : r < 1),
      Summable fun k : ℕ => ((k : ℝ) + 1) ^ d * r ^ k :=
  TateCurve.ks17_C1_exports.{0}.2.2.2.2.1

theorem rows_eval_eq_zero_of_master_at_spectators_envelope : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hmaster : ∀ n : ℕ, ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M,
          spectatorRows s a (unitSpectator q n) M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha (spectatorRows s a (unitSpectator q n)) w M
          + specTail (spectatorRows s a (unitSpectator q n)) w M
          + specGamma (spectatorRows s a (unitSpectator q n)) M),
      ∀ M k : ℕ, 1 ≤ k → k ≤ M → ∀ v : K, v ≠ 0 → ∑ j ∈ s M k, a M k j * v ^ j = 0 :=
  TateCurve.ks17_C1_exports.{u_1}.2.2.2.2.2.1

theorem master_of_hasSum_qshift_envelope : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {B : ℝ} {d : ℕ} (hB : 0 ≤ B) (c : ℕ → ℕ → K)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) {g : K → K → K}
    (hinv : ∀ q w : K, q ≠ 0 → 1 < ‖w‖ → ‖q‖ * ‖w‖ < 1 → g q (q * w) = g q w)
    (hrepr : ∀ q w : K, q ≠ 0 → ‖q‖ < ‖w‖ → ‖q‖ * ‖w‖ < 1 → ‖w‖ ≠ 1 →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)) * q ^ M) (g q w)),
      ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ → ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2) = specAlpha c w M + specTail c w M + specGamma c M :=
  TateCurve.ks17_C1_exports.{u_1}.2.2.2.2.2.2

end TateCurve

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum specTail specAlpha specGamma cauchyMulInt Fz Gz Gz_neg Gz_natCast Fz_mul_Gz tent tent_eq_sq_add_sum_Ico sum_mul_Fz_eq_sum_lines_nat cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice unitSpectator spectatorRows ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C3_exports ks17_D2_exports symAdd_sum_regional"
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

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum specTail specAlpha specGamma cauchyMulInt Fz Gz Gz_neg Gz_natCast Fz_mul_Gz tent tent_eq_sq_add_sum_Ico sum_mul_Fz_eq_sum_lines_nat cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice unitSpectator spectatorRows ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C3_exports ks17_D2_exports symAdd_sum_regional"
p2m_open "TateCurve"

theorem diffHyp_of_region_closed : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] {q τ : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v'))),
      DiffHyp q :=
  TateCurve.ks17_D2_exports.{u_1}.1

theorem exists_sqrt_of_isAlgClosed : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] [IsAlgClosed K] (q : K),
      ∃ τ : K, τ ^ 2 = q :=
  TateCurve.ks17_D2_exports.{u_1}.2.1

theorem symAdd_sum_of_region_closed : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] {q u v τ : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v),
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = symSumNum q (pointX q u) (pointX q v) :=
  TateCurve.ks17_D2_exports.{u_1}.2.2

end TateCurve

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum specTail specAlpha specGamma cauchyMulInt Fz Gz Gz_neg Gz_natCast Fz_mul_Gz tent tent_eq_sq_add_sum_Ico sum_mul_Fz_eq_sum_lines_nat cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice unitSpectator spectatorRows ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C3_exports ks17_D2_exports symAdd_sum_regional"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section OddCollapse

def gzSign (a : ℤ) (w : K) : K := if 0 ≤ a then w else -w

@[scoped simp] theorem norm_gzSign (a : ℤ) (w : K) : ‖gzSign a w‖ = ‖w‖ := by
  unfold gzSign
  split <;> simp

theorem gzSign_mul (a : ℤ) (w w' : K) : gzSign a (w * w') = gzSign a w * w' := by
  unfold gzSign
  split <;> ring

variable (u)

theorem mul_Gz_eq_gzSign_mul_Gz_natAbs (w : K) (a : ℤ) :
    w * Gz u a = gzSign a w * Gz u ((a.natAbs : ℤ)) := by
  unfold gzSign
  by_cases ha : 0 ≤ a
  · rw [if_pos ha, Int.natAbs_of_nonneg ha]
  · rw [if_neg ha]
    have hneg : ((a.natAbs : ℤ)) = -a := by omega
    rw [hneg, Gz_neg]
    ring

variable {u}

theorem sum_mul_Gz_eq_sum_rows_nat {α : Type*} (S : Finset α) (w : α → K) (g : α → ℕ) {N : ℕ}
    (hg : ∀ x ∈ S, g x ≤ N) :
    ∑ x ∈ S, w x * Gz u (g x : ℤ)
      = ∑ k ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => g x = k), w x) * Gz u (k : ℤ) := by
  have hmaps : ∀ x ∈ S, g x ∈ Finset.range (N + 1) := fun x hx =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hg x hx))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => w x * Gz u (g x : ℤ))]
  have hsplit : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have h0 : ∑ x ∈ S.filter (fun x => g x = 0), w x * Gz u (g x : ℤ) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2]
    simp
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.mp hx).2]

theorem sum_mul_Gz_eq_sum_rows_int {α : Type*} (S : Finset α) (w : α → K) (g : α → ℤ) {N : ℕ}
    (hg : ∀ x ∈ S, (g x).natAbs ≤ N) :
    ∑ x ∈ S, w x * Gz u (g x)
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => (g x).natAbs = k), gzSign (g x) (w x)) * Gz u (k : ℤ) := by
  have h : ∀ x ∈ S, w x * Gz u (g x)
      = gzSign (g x) (w x) * Gz u (((g x).natAbs : ℤ)) := fun x _ =>
    mul_Gz_eq_gzSign_mul_Gz_natAbs u (w x) (g x)
  rw [Finset.sum_congr rfl h]
  exact sum_mul_Gz_eq_sum_rows_nat S _ (fun x => (g x).natAbs) hg

theorem sum_mul_Gz_Gz_eq_sum_rows_nat {α : Type*} (S : Finset α) (w : α → K) (g h : α → ℕ)
    {N : ℕ} (hg : ∀ x ∈ S, g x ≤ N) (hh : ∀ x ∈ S, h x ≤ N) :
    ∑ x ∈ S, w x * Gz u (g x : ℤ) * Gz v (h x : ℤ)
      = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => g x = k ∧ h x = j), w x)
            * Gz u (k : ℤ) * Gz v (j : ℤ) := by
  calc ∑ x ∈ S, w x * Gz u (g x : ℤ) * Gz v (h x : ℤ)
      = ∑ x ∈ S, (w x * Gz v (h x : ℤ)) * Gz u (g x : ℤ) :=
        Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ k ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => g x = k), w x * Gz v (h x : ℤ)) * Gz u (k : ℤ) :=
        sum_mul_Gz_eq_sum_rows_nat S _ g hg
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => g x = k ∧ h x = j), w x)
            * Gz u (k : ℤ) * Gz v (j : ℤ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sum_mul_Gz_eq_sum_rows_nat (u := v) (S.filter fun x => g x = k) w h
          (fun x hx => hh x (Finset.mem_filter.mp hx).1), Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.filter_filter]
        ring

theorem sum_mul_Gz_Gz_eq_sum_rows_int {α : Type*} (S : Finset α) (w : α → K) (g h : α → ℤ)
    {N : ℕ} (hg : ∀ x ∈ S, (g x).natAbs ≤ N) (hh : ∀ x ∈ S, (h x).natAbs ≤ N) :
    ∑ x ∈ S, w x * Gz u (g x) * Gz v (h x)
      = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => (g x).natAbs = k ∧ (h x).natAbs = j),
              gzSign (h x) (gzSign (g x) (w x)))
            * Gz u (k : ℤ) * Gz v (j : ℤ) := by
  calc ∑ x ∈ S, w x * Gz u (g x) * Gz v (h x)
      = ∑ x ∈ S, gzSign (g x) (w x) * Gz u (((g x).natAbs : ℤ)) * Gz v (h x) :=
        Finset.sum_congr rfl fun x _ => by
          rw [show w x * Gz u (g x) * Gz v (h x) = (w x * Gz u (g x)) * Gz v (h x) by ring,
            mul_Gz_eq_gzSign_mul_Gz_natAbs u (w x) (g x)]
    _ = ∑ x ∈ S, gzSign (h x) (gzSign (g x) (w x)) * Gz v (((h x).natAbs : ℤ))
          * Gz u (((g x).natAbs : ℤ)) :=
        Finset.sum_congr rfl fun x _ => by
          rw [show gzSign (g x) (w x) * Gz u (((g x).natAbs : ℤ)) * Gz v (h x)
              = (gzSign (g x) (w x) * Gz v (h x)) * Gz u (((g x).natAbs : ℤ)) by ring,
            mul_Gz_eq_gzSign_mul_Gz_natAbs v (gzSign (g x) (w x)) (h x)]
    _ = ∑ x ∈ S, (gzSign (h x) (gzSign (g x) (w x))) * Gz u (((g x).natAbs : ℤ))
          * Gz v (((h x).natAbs : ℤ)) :=
        Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => (g x).natAbs = k ∧ (h x).natAbs = j),
              gzSign (h x) (gzSign (g x) (w x)))
            * Gz u (k : ℤ) * Gz v (j : ℤ) :=
        sum_mul_Gz_Gz_eq_sum_rows_nat S _ (fun x => (g x).natAbs) (fun x => (h x).natAbs) hg hh

end OddCollapse

section MonomialConversion

def monomialOfGzSupport (s : Finset ℤ) : Finset ℤ := s ∪ s.image (fun j => -j)

def monomialOfGzCoeff (s : Finset ℤ) (a : ℤ → K) (j : ℤ) : K :=
  (if j ∈ s then a j else 0) - (if -j ∈ s then a (-j) else 0)

theorem monomialOfGzSupport_image_neg (s : Finset ℤ) :
    (monomialOfGzSupport s).image (fun j => -j) = monomialOfGzSupport s := by
  unfold monomialOfGzSupport
  rw [Finset.image_union, Finset.image_image]
  have h1 : s.image ((fun j : ℤ => -j) ∘ fun j : ℤ => -j) = s := by
    rw [show ((fun j : ℤ => -j) ∘ fun j : ℤ => -j) = id by funext j; simp, Finset.image_id]
  rw [h1, Finset.union_comm]

theorem sum_monomialOfGzCoeff_zpow_eq (s : Finset ℤ) (a : ℤ → K) :
    ∑ j ∈ monomialOfGzSupport s, monomialOfGzCoeff s a j * v ^ j
      = ∑ j ∈ s, a j * Gz v j := by
  have hsub : s ⊆ monomialOfGzSupport s := Finset.subset_union_left

  have hsplit : ∑ j ∈ monomialOfGzSupport s, monomialOfGzCoeff s a j * v ^ j
      = (∑ j ∈ monomialOfGzSupport s, (if j ∈ s then a j else 0) * v ^ j)
        - ∑ j ∈ monomialOfGzSupport s, (if -j ∈ s then a (-j) else 0) * v ^ j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold monomialOfGzCoeff
    ring

  have hfst : ∑ j ∈ monomialOfGzSupport s, (if j ∈ s then a j else 0) * v ^ j
      = ∑ j ∈ s, a j * v ^ j := by
    rw [Finset.sum_congr rfl (fun j _ => by rw [ite_mul, zero_mul]),
      Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]

  have hsnd : ∑ j ∈ monomialOfGzSupport s, (if -j ∈ s then a (-j) else 0) * v ^ j
      = ∑ j ∈ s, a j * v ^ (-j) := by
    have hinj : ∀ x ∈ monomialOfGzSupport s, ∀ y ∈ monomialOfGzSupport s,
        (fun j : ℤ => -j) x = (fun j : ℤ => -j) y → x = y := fun x _ y _ h => by
      simpa using h
    calc ∑ j ∈ monomialOfGzSupport s, (if -j ∈ s then a (-j) else 0) * v ^ j
        = ∑ j ∈ (monomialOfGzSupport s).image (fun j => -j),
            (if -j ∈ s then a (-j) else 0) * v ^ j := by
          rw [monomialOfGzSupport_image_neg]
      _ = ∑ j ∈ monomialOfGzSupport s, (if -(-j) ∈ s then a (-(-j)) else 0) * v ^ (-j) :=
          Finset.sum_image hinj
      _ = ∑ j ∈ monomialOfGzSupport s, (if j ∈ s then a j else 0) * v ^ (-j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [neg_neg]
      _ = ∑ j ∈ s, a j * v ^ (-j) := by
          rw [Finset.sum_congr rfl (fun j _ => by rw [ite_mul, zero_mul]),
            Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
  rw [hsplit, hfst, hsnd, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Gz]
  ring

theorem norm_monomialOfGzCoeff_le (s : Finset ℤ) (a : ℤ → K) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) (j : ℤ) : ‖monomialOfGzCoeff s a j‖ ≤ 2 * C := by
  unfold monomialOfGzCoeff
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖if j ∈ s then a j else 0‖ ≤ C := by
    split
    · exact ha j
    · simpa using hC
  have h2 : ‖if -j ∈ s then a (-j) else 0‖ ≤ C := by
    split
    · exact ha (-j)
    · simpa using hC
  linarith

end MonomialConversion

section Composition

variable [CharZero K] [DecidableEq K]
variable {q τ : K}

theorem diffHyp_of_coeff_Gz_rows_envelope (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hrows : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      (∑ k ∈ Finset.Icc 1 M,
          (∑ j ∈ s M k, a M k j * Gz v' j) * (u' ^ k - u'⁻¹ ^ k))
        = addDefectDiffCoeff u' v' M) :
    DiffHyp q := by

  set s' : ℕ → ℕ → Finset ℤ := fun M k => monomialOfGzSupport (s M k) with hs'
  set a' : ℕ → ℕ → ℤ → K := fun M k => monomialOfGzCoeff (s M k) (a M k) with ha'

  have hbound : ∀ M k j, ‖a' M k j‖ ≤ (2 * B) * ((M : ℝ) + 1) ^ d := by
    intro M k j
    have henv : (0 : ℝ) ≤ B * ((M : ℝ) + 1) ^ d :=
      mul_nonneg hB (pow_nonneg (by positivity) d)
    have h := norm_monomialOfGzCoeff_le (s M k) (a M k) henv (fun j' => ha M k j') j
    calc ‖a' M k j‖ ≤ 2 * (B * ((M : ℝ) + 1) ^ d) := h
      _ = (2 * B) * ((M : ℝ) + 1) ^ d := by ring

  have hrows' : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      (∑ k ∈ Finset.Icc 1 M,
          (∑ j ∈ s' M k, a' M k j * v' ^ j) * (u' ^ k - u'⁻¹ ^ k))
        = addDefectDiffCoeff u' v' M := by
    intro q' u' v' hreg M
    rw [← hrows q' u' v' hreg M]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_monomialOfGzCoeff_zpow_eq (s M k) (a M k)]

  refine diffHyp_of_region_closed hq0 hq hτ hregS1 ?_
  intro u' v' hreg
  refine diff_identity_of_rowExpansion_odd_envelope (B := 2 * B) (d := d) (s := s') (a := a')
    (by linarith) hbound ?_ hreg
  exact diffExpansion_of_coeff_eq
    (f := fun u' v' M =>
      ∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s' M k, a' M k j * v' ^ j) * (u' ^ k - u'⁻¹ ^ k))
    hrows'

theorem diffHyp_of_canonical_square (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {w : ℕ → ℕ → ℕ → K} (hw : ∀ M k j, ‖w M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hsq : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      addDefectDiffCoeff u' v' M
        = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            w M k j * Gz u' (k : ℤ) * Gz v' (j : ℤ)) :
    DiffHyp q := by
  refine diffHyp_of_coeff_Gz_rows_envelope hq0 hq hτ hregS1 (d := d) hB
    (s := fun M _ => (Finset.Icc 1 M).image ((↑·) : ℕ → ℤ))
    (a := fun M k j => if 0 ≤ j then w M k j.toNat else 0) ?_ ?_
  ·
    intro M k j
    by_cases hj : 0 ≤ j
    · simpa only [if_pos hj] using hw M k j.toNat
    · simp only [if_neg hj, norm_zero]
      exact mul_nonneg hB (pow_nonneg (by positivity) d)
  ·
    intro q' u' v' hreg M
    rw [hsq q' u' v' hreg M]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [show (u' ^ k - u'⁻¹ ^ k) = Gz u' (k : ℤ) from (Gz_natCast u' k).symm,
      Finset.sum_mul, Finset.sum_image (fun x _ y _ h => Nat.cast_injective h)]
    refine Finset.sum_congr rfl fun j hj => ?_
    beta_reduce
    rw [if_pos (Int.natCast_nonneg j), Int.toNat_natCast]
    ring

theorem diffHyp_of_coeff_Gz_rows_envelope_of_isAlgClosed [IsAlgClosed K]
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hrows : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      (∑ k ∈ Finset.Icc 1 M,
          (∑ j ∈ s M k, a M k j * Gz v' j) * (u' ^ k - u'⁻¹ ^ k))
        = addDefectDiffCoeff u' v' M) :
    DiffHyp q := by
  obtain ⟨τ, hτ⟩ := exists_sqrt_of_isAlgClosed q
  exact diffHyp_of_coeff_Gz_rows_envelope hq0 hq hτ hregS1 hB ha hrows

end Composition

section PsiBlock

def psiBlockIdx (M : ℕ) : Finset (Σ _ : (Σ _ : ℕ, ℕ), ℕ) :=
  ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => (M - p.1).divisors

theorem bounds_of_mem_psiBlockIdx {M : ℕ} {x : Σ _ : (Σ _ : ℕ, ℕ), ℕ}
    (hx : x ∈ psiBlockIdx M) : 1 ≤ x.1.2 ∧ x.1.2 ≤ M ∧ 1 ≤ x.2 ∧ x.2 ≤ M := by
  have h1 := Finset.mem_sigma.mp hx
  have h2 := Finset.mem_sigma.mp h1.1
  have hi : 1 ≤ x.1.1 ∧ x.1.1 < M := Finset.mem_Ico.mp h2.1
  have hd := Nat.mem_divisors.mp h2.2
  have he := Nat.mem_divisors.mp h1.2
  have hd1 : 1 ≤ x.1.2 := Nat.pos_of_mem_divisors h2.2
  have he1 : 1 ≤ x.2 := Nat.pos_of_mem_divisors h1.2
  have hdM : x.1.2 ≤ x.1.1 := Nat.le_of_dvd (by omega) hd.1
  have heM : x.2 ≤ M - x.1.1 := Nat.le_of_dvd (by omega) he.1
  exact ⟨hd1, by omega, he1, by omega⟩

theorem cauchyMulInt_psiCoeffFull_eq_sum_rows (u v : K) (M : ℕ) :
    cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ x ∈ (psiBlockIdx M).filter (fun x => x.1.2 = k ∧ x.2 = j),
              ((x.1.2 : K)) ^ 2 * ((x.2 : K)) ^ 2)
            * Gz u (k : ℤ) * Gz v (j : ℤ) :=
  calc cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M
      = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ e ∈ (M - i).divisors,
          (d : K) ^ 2 * (e : K) ^ 2 * (Gz u (d : ℤ) * Gz v (e : ℤ)) :=
        cauchyMulInt_psiCoeffFull_eq_rows u v M
    _ = ∑ x ∈ psiBlockIdx M,
          ((x.1.2 : K)) ^ 2 * ((x.2 : K)) ^ 2 * (Gz u (x.1.2 : ℤ) * Gz v (x.2 : ℤ)) :=
        sum_nest3_eq_sigma (Finset.Ico 1 M) (fun i => i.divisors)
          (fun i _ => (M - i).divisors)
          (fun _ d e => (d : K) ^ 2 * (e : K) ^ 2 * (Gz u (d : ℤ) * Gz v (e : ℤ)))
    _ = ∑ x ∈ psiBlockIdx M,
          ((x.1.2 : K)) ^ 2 * ((x.2 : K)) ^ 2 * Gz u (x.1.2 : ℤ) * Gz v (x.2 : ℤ) :=
        Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ x ∈ (psiBlockIdx M).filter (fun x => x.1.2 = k ∧ x.2 = j),
              ((x.1.2 : K)) ^ 2 * ((x.2 : K)) ^ 2)
            * Gz u (k : ℤ) * Gz v (j : ℤ) :=
        sum_mul_Gz_Gz_eq_sum_rows_nat (psiBlockIdx M)
          (fun x => ((x.1.2 : K)) ^ 2 * ((x.2 : K)) ^ 2) (fun x => x.1.2) (fun x => x.2)
          (fun x hx => (bounds_of_mem_psiBlockIdx hx).2.1)
          (fun x hx => (bounds_of_mem_psiBlockIdx hx).2.2.2)

end PsiBlock

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum specTail specAlpha specGamma cauchyMulInt Fz Gz Gz_neg Gz_natCast Fz_mul_Gz tent tent_eq_sq_add_sum_Ico sum_mul_Fz_eq_sum_lines_nat cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice unitSpectator spectatorRows ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C3_exports ks17_D2_exports symAdd_sum_regional"
p2m_open "TateCurve"

open IsUltrametricDist

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section CanonicalTable

variable (K) in

def HasCanonicalTable (f : K → K → ℕ → K) : Prop :=
  ∃ w : ℕ → ℕ → ℕ → K, (∀ M k j, ‖w M k j‖ ≤ 1) ∧
    ∀ u v : K, u ≠ 0 → v ≠ 0 → u ≠ 1 → v ≠ 1 → u * v ≠ 1 → u * v⁻¹ ≠ 1 → ∀ M : ℕ, 0 < M →
      f u v M = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
        w M k j * Gz u (k : ℤ) * Gz v (j : ℤ)

namespace HasCanonicalTable

variable {f g : K → K → ℕ → K}

theorem congr (hfg : ∀ u v : K, u ≠ 0 → v ≠ 0 → u ≠ 1 → v ≠ 1 → u * v ≠ 1 → u * v⁻¹ ≠ 1 →
    ∀ M : ℕ, 0 < M → f u v M = g u v M) (hf : HasCanonicalTable K f) :
    HasCanonicalTable K g := by
  obtain ⟨w, hw, hrow⟩ := hf
  exact ⟨w, hw, fun u v hu hv hu1 hv1 hm hd M hM =>
    (hfg u v hu hv hu1 hv1 hm hd M hM) ▸ hrow u v hu hv hu1 hv1 hm hd M hM⟩

theorem zero : HasCanonicalTable K fun _ _ _ => 0 :=
  ⟨fun _ _ _ => 0, fun _ _ _ => by simp, fun _ _ _ _ _ _ _ _ _ _ => by simp⟩

theorem add (hf : HasCanonicalTable K f) (hg : HasCanonicalTable K g) :
    HasCanonicalTable K fun u v M => f u v M + g u v M := by
  obtain ⟨w₁, hw₁, hrow₁⟩ := hf
  obtain ⟨w₂, hw₂, hrow₂⟩ := hg
  refine ⟨fun M k j => w₁ M k j + w₂ M k j, fun M k j =>
    (norm_add_le_max _ _).trans (max_le (hw₁ M k j) (hw₂ M k j)), ?_⟩
  intro u v hu hv hu1 hv1 hm hd M hM
  beta_reduce
  rw [hrow₁ u v hu hv hu1 hv1 hm hd M hM, hrow₂ u v hu hv hu1 hv1 hm hd M hM,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem neg (hf : HasCanonicalTable K f) : HasCanonicalTable K fun u v M => -(f u v M) := by
  obtain ⟨w, hw, hrow⟩ := hf
  refine ⟨fun M k j => -(w M k j), fun M k j => by simpa using hw M k j, ?_⟩
  intro u v hu hv hu1 hv1 hm hd M hM
  beta_reduce
  rw [hrow u v hu hv hu1 hv1 hm hd M hM, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sub (hf : HasCanonicalTable K f) (hg : HasCanonicalTable K g) :
    HasCanonicalTable K fun u v M => f u v M - g u v M :=
  (hf.add hg.neg).congr fun _ _ _ _ _ _ _ _ _ _ => by ring

theorem const_mul (c : K) (hc : ‖c‖ ≤ 1) (hf : HasCanonicalTable K f) :
    HasCanonicalTable K fun u v M => c * f u v M := by
  obtain ⟨w, hw, hrow⟩ := hf
  refine ⟨fun M k j => c * w M k j, fun M k j => by
    calc ‖c * w M k j‖ = ‖c‖ * ‖w M k j‖ := norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul hc (hw M k j) (norm_nonneg _) zero_le_one
      _ = 1 := by norm_num, ?_⟩
  intro u v hu hv hu1 hv1 hm hd M hM
  beta_reduce
  rw [hrow u v hu hv hu1 hv1 hm hd M hM, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end HasCanonicalTable
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

end CanonicalTable
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

section Workhorses

theorem norm_filterSum_gzSign_le_one {α : Type*} (S : Finset α) (p : α → Prop) [DecidablePred p]
    (g h : α → ℤ) (w : α → K) (hw : ∀ x ∈ S, ‖w x‖ ≤ 1) :
    ‖∑ x ∈ S.filter p, gzSign (h x) (gzSign (g x) (w x))‖ ≤ 1 :=
  norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x hx => by
    rw [norm_gzSign, norm_gzSign]
    exact hw x (Finset.mem_filter.mp hx).1

theorem hasCanonicalTable_of_atoms {α : Type*} (S : ℕ → Finset α) (c : ℕ → α → K)
    (gu gv : ℕ → α → ℤ)
    (hgu : ∀ M, ∀ x ∈ S M, (gu M x).natAbs ≤ M) (hgv : ∀ M, ∀ x ∈ S M, (gv M x).natAbs ≤ M)
    (hc : ∀ M, ∀ x ∈ S M, ‖c M x‖ ≤ 1) {f : K → K → ℕ → K}
    (hf : ∀ u v : K, u ≠ 0 → v ≠ 0 → u ≠ 1 → v ≠ 1 → u * v ≠ 1 → u * v⁻¹ ≠ 1 → ∀ M : ℕ,
      0 < M → f u v M = ∑ x ∈ S M, c M x * Gz u (gu M x) * Gz v (gv M x)) :
    HasCanonicalTable K f := by
  refine ⟨fun M k j => ∑ x ∈ (S M).filter
      (fun x => (gu M x).natAbs = k ∧ (gv M x).natAbs = j),
      gzSign (gv M x) (gzSign (gu M x) (c M x)),
    fun M k j => norm_filterSum_gzSign_le_one (S M) _ _ _ _ (hc M), ?_⟩
  intro u v hu hv hu1 hv1 hm hd M hM
  rw [hf u v hu hv hu1 hv1 hm hd M hM]
  exact sum_mul_Gz_Gz_eq_sum_rows_int (S M) (c M) (gu M) (gv M) (hgu M) (hgv M)

theorem hasCanonicalTable_of_rows {α β γ : Type*} (S : ℕ → Finset α) (c : ℕ → α → K)
    (Tu : ℕ → α → Finset β) (au : ℕ → α → β → K) (gu : ℕ → α → β → ℤ)
    (Tv : ℕ → α → Finset γ) (av : ℕ → α → γ → K) (gv : ℕ → α → γ → ℤ)
    (hgu : ∀ M, ∀ x ∈ S M, ∀ i ∈ Tu M x, (gu M x i).natAbs ≤ M)
    (hgv : ∀ M, ∀ x ∈ S M, ∀ j ∈ Tv M x, (gv M x j).natAbs ≤ M)
    (hc : ∀ M, ∀ x ∈ S M, ∀ i ∈ Tu M x, ∀ j ∈ Tv M x, ‖c M x * au M x i * av M x j‖ ≤ 1)
    {f : K → K → ℕ → K}
    (hf : ∀ u v : K, u ≠ 0 → v ≠ 0 → u ≠ 1 → v ≠ 1 → u * v ≠ 1 → u * v⁻¹ ≠ 1 → ∀ M : ℕ,
      0 < M → f u v M = ∑ x ∈ S M, c M x
        * (∑ i ∈ Tu M x, au M x i * Gz u (gu M x i))
        * (∑ j ∈ Tv M x, av M x j * Gz v (gv M x j))) :
    HasCanonicalTable K f := by
  refine hasCanonicalTable_of_atoms
    (fun M => ((S M).sigma (Tu M)).sigma (fun p => Tv M p.1))
    (fun M y => c M y.1.1 * au M y.1.1 y.1.2 * av M y.1.1 y.2)
    (fun M y => gu M y.1.1 y.1.2) (fun M y => gv M y.1.1 y.2)
    (fun M y hy => ?_) (fun M y hy => ?_) (fun M y hy => ?_) ?_
  · have h1 := Finset.mem_sigma.mp hy
    have h2 := Finset.mem_sigma.mp h1.1
    exact hgu M y.1.1 h2.1 y.1.2 h2.2
  · have h1 := Finset.mem_sigma.mp hy
    have h2 := Finset.mem_sigma.mp h1.1
    exact hgv M y.1.1 h2.1 y.2 h1.2
  · have h1 := Finset.mem_sigma.mp hy
    have h2 := Finset.mem_sigma.mp h1.1
    exact hc M y.1.1 h2.1 y.1.2 h2.2 y.2 h1.2
  · intro u v hu hv hu1 hv1 hm hd M hM
    beta_reduce
    rw [hf u v hu hv hu1 hv1 hm hd M hM]
    calc ∑ x ∈ S M, c M x * (∑ i ∈ Tu M x, au M x i * Gz u (gu M x i))
          * (∑ j ∈ Tv M x, av M x j * Gz v (gv M x j))
        = ∑ x ∈ S M, ∑ i ∈ Tu M x, ∑ j ∈ Tv M x,
            c M x * au M x i * av M x j * Gz u (gu M x i) * Gz v (gv M x j) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum (a := c M x), Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ p ∈ (S M).sigma (Tu M), ∑ j ∈ Tv M p.1,
            c M p.1 * au M p.1 p.2 * av M p.1 j * Gz u (gu M p.1 p.2) * Gz v (gv M p.1 j) :=
          Finset.sum_sigma' (S M) (Tu M) _
      _ = ∑ y ∈ ((S M).sigma (Tu M)).sigma (fun p => Tv M p.1),
            c M y.1.1 * au M y.1.1 y.1.2 * av M y.1.1 y.2 * Gz u (gu M y.1.1 y.1.2)
              * Gz v (gv M y.1.1 y.2) :=
          Finset.sum_sigma' ((S M).sigma (Tu M)) (fun p => Tv M p.1) _

theorem norm_mul_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg b) hb

theorem norm_pow_le_one {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg a) ha

theorem norm_sub_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (norm_add_le_max a (-b)).trans (max_le ha (by simpa using hb))

theorem norm_two_le_one : ‖(2 : K)‖ ≤ 1 := by
  simpa using norm_natCast_le_one K 2

theorem norm_neg_le_one {a : K} (ha : ‖a‖ ≤ 1) : ‖-a‖ ≤ 1 := by simpa using ha

end Workhorses
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

section PsiBlockTable

theorem hasCanonicalTable_psiBlock :
    HasCanonicalTable K fun u v M => cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M := by
  refine hasCanonicalTable_of_atoms (fun M => psiBlockIdx M)
    (fun _ x => ((x.1.2 : K)) ^ 2 * ((x.2 : K)) ^ 2)
    (fun _ x => (x.1.2 : ℤ)) (fun _ x => (x.2 : ℤ))
    (fun M x hx => ?_) (fun M x hx => ?_) (fun M x hx => ?_) ?_
  · simpa using (bounds_of_mem_psiBlockIdx hx).2.1
  · simpa using (bounds_of_mem_psiBlockIdx hx).2.2.2
  · exact norm_mul_le_one (norm_pow_le_one (norm_natCast_le_one K _) 2)
      (norm_pow_le_one (norm_natCast_le_one K _) 2)
  · intro u v hu hv hu1 hv1 hm hd M hM
    calc cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M
        = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ e ∈ (M - i).divisors,
            (d : K) ^ 2 * (e : K) ^ 2 * (Gz u (d : ℤ) * Gz v (e : ℤ)) :=
          cauchyMulInt_psiCoeffFull_eq_rows u v M
      _ = ∑ x ∈ psiBlockIdx M,
            ((x.1.2 : K)) ^ 2 * ((x.2 : K)) ^ 2 * (Gz u (x.1.2 : ℤ) * Gz v (x.2 : ℤ)) :=
          sum_nest3_eq_sigma (Finset.Ico 1 M) (fun i => i.divisors)
            (fun i _ => (M - i).divisors)
            (fun _ d e => (d : K) ^ 2 * (e : K) ^ 2 * (Gz u (d : ℤ) * Gz v (e : ℤ)))
      _ = ∑ x ∈ psiBlockIdx M,
            ((x.1.2 : K)) ^ 2 * ((x.2 : K)) ^ 2 * Gz u (x.1.2 : ℤ) * Gz v (x.2 : ℤ) :=
          Finset.sum_congr rfl fun x _ => by ring

end PsiBlockTable
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

section CrossBlockTable

theorem add_le_of_mem_psiBlockIdx {M : ℕ} {x : Σ _ : (Σ _ : ℕ, ℕ), ℕ}
    (hx : x ∈ psiBlockIdx M) : x.1.2 + x.2 ≤ M := by
  have h1 := Finset.mem_sigma.mp hx
  have h2 := Finset.mem_sigma.mp h1.1
  have hi : 1 ≤ x.1.1 ∧ x.1.1 < M := Finset.mem_Ico.mp h2.1
  have hd := Nat.mem_divisors.mp h2.2
  have he := Nat.mem_divisors.mp h1.2
  have hdM : x.1.2 ≤ x.1.1 := Nat.le_of_dvd (by omega) hd.1
  have heM : x.2 ≤ M - x.1.1 := Nat.le_of_dvd (by omega) he.1
  omega

def crossBlockIdx (M : ℕ) : Finset (Σ _ : Σ _ : (Σ _ : ℕ, ℕ), ℕ, ℕ × ℕ) :=
  (psiBlockIdx M).sigma fun x => Finset.range x.1.2 ×ˢ Finset.range x.2

theorem bounds_of_mem_crossBlockIdx {M : ℕ} {y : Σ _ : Σ _ : (Σ _ : ℕ, ℕ), ℕ, ℕ × ℕ}
    (hy : y ∈ crossBlockIdx M) :
    1 ≤ y.1.1.2 ∧ 1 ≤ y.1.2 ∧ y.1.1.2 + y.1.2 ≤ M ∧ y.2.1 < y.1.1.2 ∧ y.2.2 < y.1.2 := by
  have h1 := Finset.mem_sigma.mp hy
  have h2 := Finset.mem_product.mp h1.2
  have h3 := bounds_of_mem_psiBlockIdx h1.1
  have h4 := add_le_of_mem_psiBlockIdx h1.1
  exact ⟨h3.1, h3.2.2.1, h4, Finset.mem_range.mp h2.1, Finset.mem_range.mp h2.2⟩

theorem hasCanonicalTable_crossBlock :
    HasCanonicalTable K fun u v M =>
      ∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ e ∈ (M - b).divisors,
        (d : K) * (e : K)
          * ∑ i ∈ Finset.range d, ∑ i' ∈ Finset.range e,
              (Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - d - e)
                - Gz u ((i : ℤ) + i' + 1 - e) * Gz v ((i : ℤ) + i' + 1 - d)) := by
  have hpos : HasCanonicalTable K fun u v M => ∑ y ∈ crossBlockIdx M,
      ((y.1.1.2 : K) * (y.1.2 : K)) * Gz u ((y.2.1 : ℤ) + y.2.2 + 1)
        * Gz v ((y.2.1 : ℤ) + y.2.2 + 1 - y.1.1.2 - y.1.2) := by
    refine hasCanonicalTable_of_atoms (fun M => crossBlockIdx M)
      (fun _ y => (y.1.1.2 : K) * (y.1.2 : K))
      (fun _ y => (y.2.1 : ℤ) + y.2.2 + 1)
      (fun _ y => (y.2.1 : ℤ) + y.2.2 + 1 - y.1.1.2 - y.1.2)
      (fun M y hy => ?_) (fun M y hy => ?_)
      (fun M y hy => norm_mul_le_one (norm_natCast_le_one K _) (norm_natCast_le_one K _))
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)
    · have h := bounds_of_mem_crossBlockIdx hy
      beta_reduce
      omega
    · have h := bounds_of_mem_crossBlockIdx hy
      beta_reduce
      omega
  have hneg : HasCanonicalTable K fun u v M => ∑ y ∈ crossBlockIdx M,
      ((y.1.1.2 : K) * (y.1.2 : K)) * Gz u ((y.2.1 : ℤ) + y.2.2 + 1 - y.1.2)
        * Gz v ((y.2.1 : ℤ) + y.2.2 + 1 - y.1.1.2) := by
    refine hasCanonicalTable_of_atoms (fun M => crossBlockIdx M)
      (fun _ y => (y.1.1.2 : K) * (y.1.2 : K))
      (fun _ y => (y.2.1 : ℤ) + y.2.2 + 1 - y.1.2)
      (fun _ y => (y.2.1 : ℤ) + y.2.2 + 1 - y.1.1.2)
      (fun M y hy => ?_) (fun M y hy => ?_)
      (fun M y hy => norm_mul_le_one (norm_natCast_le_one K _) (norm_natCast_le_one K _))
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)
    · have h := bounds_of_mem_crossBlockIdx hy
      beta_reduce
      omega
    · have h := bounds_of_mem_crossBlockIdx hy
      beta_reduce
      omega
  refine (hpos.sub hneg).congr ?_
  intro u v hu hv hu1 hv1 hm hd M hM
  beta_reduce
  rw [← Finset.sum_sub_distrib]
  calc ∑ y ∈ crossBlockIdx M,
        (((y.1.1.2 : K) * (y.1.2 : K)) * Gz u ((y.2.1 : ℤ) + y.2.2 + 1)
            * Gz v ((y.2.1 : ℤ) + y.2.2 + 1 - y.1.1.2 - y.1.2)
          - ((y.1.1.2 : K) * (y.1.2 : K)) * Gz u ((y.2.1 : ℤ) + y.2.2 + 1 - y.1.2)
            * Gz v ((y.2.1 : ℤ) + y.2.2 + 1 - y.1.1.2))
      = ∑ x ∈ psiBlockIdx M, ∑ p ∈ Finset.range x.1.2 ×ˢ Finset.range x.2,
          (((x.1.2 : K) * (x.2 : K)) * Gz u ((p.1 : ℤ) + p.2 + 1)
              * Gz v ((p.1 : ℤ) + p.2 + 1 - x.1.2 - x.2)
            - ((x.1.2 : K) * (x.2 : K)) * Gz u ((p.1 : ℤ) + p.2 + 1 - x.2)
              * Gz v ((p.1 : ℤ) + p.2 + 1 - x.1.2)) :=
        (Finset.sum_sigma' (psiBlockIdx M) (fun x => Finset.range x.1.2 ×ˢ Finset.range x.2)
          (fun x p => ((x.1.2 : K) * (x.2 : K)) * Gz u ((p.1 : ℤ) + p.2 + 1)
              * Gz v ((p.1 : ℤ) + p.2 + 1 - x.1.2 - x.2)
            - ((x.1.2 : K) * (x.2 : K)) * Gz u ((p.1 : ℤ) + p.2 + 1 - x.2)
              * Gz v ((p.1 : ℤ) + p.2 + 1 - x.1.2))).symm
    _ = ∑ x ∈ psiBlockIdx M, ((x.1.2 : K) * (x.2 : K))
          * ∑ i ∈ Finset.range x.1.2, ∑ i' ∈ Finset.range x.2,
              (Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - x.1.2 - x.2)
                - Gz u ((i : ℤ) + i' + 1 - x.2) * Gz v ((i : ℤ) + i' + 1 - x.1.2)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.sum_product]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i' _ => by ring
    _ = ∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ e ∈ (M - b).divisors,
          (d : K) * (e : K)
            * ∑ i ∈ Finset.range d, ∑ i' ∈ Finset.range e,
                (Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - d - e)
                  - Gz u ((i : ℤ) + i' + 1 - e) * Gz v ((i : ℤ) + i' + 1 - d)) :=
        (sum_nest3_eq_sigma (Finset.Ico 1 M) (fun i => i.divisors)
          (fun i _ => (M - i).divisors)
          (fun _ d e => (d : K) * (e : K)
            * ∑ i ∈ Finset.range d, ∑ i' ∈ Finset.range e,
                (Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - d - e)
                  - Gz u ((i : ℤ) + i' + 1 - e) * Gz v ((i : ℤ) + i' + 1 - d)))).symm

end CrossBlockTable
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

section CrossInteriorTable

noncomputable def fgCoeff (t : ℕ) : K := if t = 0 then 1 else if t = 1 then -1 else -2

def fgIdx (a c : ℤ) (t : ℕ) : ℤ := if t = 0 then a + c else if t = 1 then a - c else c

theorem Fz_mul_Gz_eq_row {w : K} (hw : w ≠ 0) (a c : ℤ) :
    Fz w a * Gz w c = ∑ t ∈ Finset.range 3, fgCoeff t * Gz w (fgIdx a c t) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fgCoeff, fgIdx]
  norm_num
  linear_combination Fz_mul_Gz hw a c

theorem norm_fgCoeff_le_one (t : ℕ) : ‖(fgCoeff t : K)‖ ≤ 1 := by
  have h1 : ‖(1 : K)‖ ≤ 1 := by simp
  unfold fgCoeff
  split
  · exact h1
  · split
    · exact norm_neg_le_one h1
    · exact norm_neg_le_one norm_two_le_one

theorem natAbs_fgIdx_le {a c : ℤ} {N : ℕ} (ha : a.natAbs + c.natAbs ≤ N) (t : ℕ) :
    (fgIdx a c t).natAbs ≤ N := by
  unfold fgIdx
  split
  · omega
  · split <;> omega

noncomputable def ffgCoeff (t : ℕ) : K :=
  if t = 0 then 1 else if t = 1 then -1 else if t = 2 then 1 else if t = 3 then -1 else
  if t = 4 then -2 else if t = 5 then 2 else if t = 6 then -2 else if t = 7 then 2 else 4

def ffgIdx (a b c : ℤ) (t : ℕ) : ℤ :=
  if t = 0 then a + b + c else if t = 1 then a + b - c else if t = 2 then a - b + c else
  if t = 3 then a - b - c else if t = 4 then a + c else if t = 5 then a - c else
  if t = 6 then b + c else if t = 7 then b - c else c

theorem Fz_mul_Fz_mul_Gz_eq_row {w : K} (hw : w ≠ 0) (a b c : ℤ) :
    Fz w a * Fz w b * Gz w c = ∑ t ∈ Finset.range 9, ffgCoeff t * Gz w (ffgIdx a b c t) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ffgCoeff, ffgIdx]
  norm_num
  linear_combination Fz_mul_Fz_mul_Gz hw a b c

theorem norm_ffgCoeff_le_one (t : ℕ) : ‖(ffgCoeff t : K)‖ ≤ 1 := by
  have h1 : ‖(1 : K)‖ ≤ 1 := by simp
  have h2 : ‖(-2 : K)‖ ≤ 1 := norm_neg_le_one norm_two_le_one
  have h4 : ‖(4 : K)‖ ≤ 1 := by simpa using norm_natCast_le_one K 4
  unfold ffgCoeff
  repeat' split
  all_goals first
    | exact h1
    | exact norm_neg_le_one h1
    | exact h2
    | exact norm_two_le_one
    | exact h4

theorem natAbs_ffgIdx_le {a b c : ℤ} {N : ℕ} (h : a.natAbs + b.natAbs + c.natAbs ≤ N) (t : ℕ) :
    (ffgIdx a b c t).natAbs ≤ N := by
  unfold ffgIdx
  repeat' split
  all_goals omega

end CrossInteriorTable
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

section Total

theorem hasCanonicalTable_addDefectDiffCoeff
    (hci : HasCanonicalTable K fun u v M =>
      ∑ b ∈ Finset.Ico 1 M, (∑ d ∈ b.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
        * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
            (fun i => xCoeffFull u i - xCoeffFull v i) (M - b))
    (hsv : HasCanonicalTable K fun u v M => svComplex u v M) :
    HasCanonicalTable K fun u v M => addDefectDiffCoeff u v M := by
  refine (((hasCanonicalTable_crossBlock.add hci).add hasCanonicalTable_psiBlock).add
    hsv).congr ?_
  intro u v hu hv hu1 hv1 hm hd M hM
  beta_reduce
  exact (addDefectDiffCoeff_eq_absorbed hu hv hm hd hM).symm

theorem expansionRegion_side_conditions {q u v : K} (hreg : ExpansionRegion q u v) :
    u ≠ 0 ∧ v ≠ 0 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u * v ≠ 1 ∧ u * v⁻¹ ≠ 1 := by
  refine ⟨hreg.params.u_ne_zero, hreg.params.v_ne_zero, ?_, ?_, ?_, ?_⟩
  · have h := hreg.params.offLattice_u 0
    rwa [zpow_zero, one_mul] at h
  · have h := hreg.params.offLattice_v 0
    rwa [zpow_zero, one_mul] at h
  · have h := hreg.params.offLattice_mul 0
    rwa [zpow_zero, one_mul] at h
  · have h := hreg.params.offLattice_div 0
    rwa [zpow_zero, one_mul] at h

variable [CharZero K] [DecidableEq K] {q τ : K}

theorem diffHyp_of_hasCanonicalTable (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (htable : HasCanonicalTable K fun u v M => addDefectDiffCoeff u v M) :
    DiffHyp q := by
  obtain ⟨w, hw, hrow⟩ := htable
  refine diffHyp_of_canonical_square hq0 hq hτ hregS1 (B := 1) (d := 0) zero_le_one
    (w := w) (fun M k j => by simpa using hw M k j) ?_
  intro q' u' v' hreg M
  obtain ⟨hu, hv, hu1, hv1, hm, hd⟩ := expansionRegion_side_conditions hreg
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · rw [addDefectDiffCoeff_zero hu hv hu1 hv1 hm hd]
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) by rfl]
    simp
  · exact hrow u' v' hu hv hu1 hv1 hm hd M hM

theorem diffHyp_of_regional_S1_of_blocks (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hci : HasCanonicalTable K fun u v M =>
      ∑ b ∈ Finset.Ico 1 M, (∑ d ∈ b.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
        * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
            (fun i => xCoeffFull u i - xCoeffFull v i) (M - b))
    (hsv : HasCanonicalTable K fun u v M => svComplex u v M) :
    DiffHyp q :=
  diffHyp_of_hasCanonicalTable hq0 hq hτ hregS1 (hasCanonicalTable_addDefectDiffCoeff hci hsv)

end Total
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams addDefectSum specTail specAlpha specGamma cauchyMulInt Fz Gz Gz_neg Gz_natCast Fz_mul_Gz tent tent_eq_sq_add_sum_Ico sum_mul_Fz_eq_sum_lines_nat cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice unitSpectator spectatorRows ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C3_exports ks17_D2_exports symAdd_sum_regional"
p2m_open "TateCurve"

open IsUltrametricDist

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section RowReadings

theorem fgRow_eval {w : K} (hw : w ≠ 0) (a c : ℤ) :
    ∑ t ∈ Finset.range 3, fgCoeff t * Gz w (fgIdx a c t)
      = Gz w (a + c) - Gz w (a - c) - 2 * Gz w c :=
  (Fz_mul_Gz_eq_row hw a c).symm.trans (Fz_mul_Gz hw a c)

theorem ffgRow_eval {w : K} (hw : w ≠ 0) (a b c : ℤ) :
    ∑ t ∈ Finset.range 9, ffgCoeff t * Gz w (ffgIdx a b c t)
      = Gz w (a + b + c) - Gz w (a + b - c) + Gz w (a - b + c) - Gz w (a - b - c)
        - 2 * Gz w (a + c) + 2 * Gz w (a - c) - 2 * Gz w (b + c) + 2 * Gz w (b - c)
        + 4 * Gz w c :=
  (Fz_mul_Fz_mul_Gz_eq_row hw a b c).symm.trans (Fz_mul_Fz_mul_Gz hw a b c)

theorem Gz_one_mul_telescope_succ_eq_sum (w : K) (hw0 : w ≠ 0) (i : ℕ) :
    Gz w 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent w (i - 2 * j)
      = ∑ k ∈ Finset.Ico 1 (i + 1), (((i + 1 : ℕ) : K) - (k : K)) * Gz w (k : ℤ) := by
  have halign : ∑ j ∈ Finset.range ((i + 1) / 2), tent w (i + 1 - 1 - 2 * j)
      = ∑ j ∈ Finset.range ((i + 1) / 2), tent w (i - 2 * j) :=
    Finset.sum_congr rfl fun j _ => by norm_num
  rw [← halign]
  exact Gz_one_mul_telescope_eq_sum w hw0 (i + 1)

theorem aColumn_eq_row (w : K) (hw : w ≠ 0) (d : ℕ) :
    ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K))
        * (Gz w 1 * ∑ j ∈ Finset.range (i / 2), tent w (i - 1 - 2 * j))
      = ∑ p ∈ (Finset.Ico 1 d).sigma (fun i => Finset.Ico 1 i),
          ((d : K) - (p.1 : K)) * ((p.1 : K) - (p.2 : K)) * Gz w (p.2 : ℤ) :=
  calc ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K))
          * (Gz w 1 * ∑ j ∈ Finset.range (i / 2), tent w (i - 1 - 2 * j))
      = ∑ i ∈ Finset.Ico 1 d, ∑ k ∈ Finset.Ico 1 i,
          ((d : K) - (i : K)) * ((i : K) - (k : K)) * Gz w (k : ℤ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Gz_one_mul_telescope_eq_sum w hw i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ p ∈ (Finset.Ico 1 d).sigma (fun i => Finset.Ico 1 i),
          ((d : K) - (p.1 : K)) * ((p.1 : K) - (p.2 : K)) * Gz w (p.2 : ℤ) :=
        Finset.sum_sigma' (Finset.Ico 1 d) (fun i => Finset.Ico 1 i)
          (fun i k => ((d : K) - (i : K)) * ((i : K) - (k : K)) * Gz w (k : ℤ))

theorem Gz_mul_tentTail_eq_row (w : K) (hw : w ≠ 0) (d f : ℕ) :
    Gz w (d : ℤ) * (∑ j ∈ Finset.Ico 1 f, ((f - j : ℕ) : K) * Fz w (j : ℤ))
      = ∑ p ∈ Finset.Ico 1 f ×ˢ Finset.range 3,
          ((f - p.1 : ℕ) : K) * fgCoeff p.2 * Gz w (fgIdx (p.1 : ℤ) (d : ℤ) p.2) :=
  calc Gz w (d : ℤ) * (∑ j ∈ Finset.Ico 1 f, ((f - j : ℕ) : K) * Fz w (j : ℤ))
      = ∑ j ∈ Finset.Ico 1 f, Gz w (d : ℤ) * (((f - j : ℕ) : K) * Fz w (j : ℤ)) := by
        rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.Ico 1 f, ∑ t ∈ Finset.range 3,
          ((f - j : ℕ) : K) * fgCoeff t * Gz w (fgIdx (j : ℤ) (d : ℤ) t) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        calc Gz w (d : ℤ) * (((f - j : ℕ) : K) * Fz w (j : ℤ))
            = ((f - j : ℕ) : K) * (Fz w (j : ℤ) * Gz w (d : ℤ)) := by ring
          _ = ((f - j : ℕ) : K) * ∑ t ∈ Finset.range 3,
                fgCoeff t * Gz w (fgIdx (j : ℤ) (d : ℤ) t) := by
              rw [Fz_mul_Gz_eq_row hw (j : ℤ) (d : ℤ)]
          _ = ∑ t ∈ Finset.range 3,
                ((f - j : ℕ) : K) * (fgCoeff t * Gz w (fgIdx (j : ℤ) (d : ℤ) t)) := by
              rw [Finset.mul_sum]
          _ = ∑ t ∈ Finset.range 3,
                ((f - j : ℕ) : K) * fgCoeff t * Gz w (fgIdx (j : ℤ) (d : ℤ) t) :=
              Finset.sum_congr rfl fun t _ => by ring
    _ = ∑ p ∈ Finset.Ico 1 f ×ˢ Finset.range 3,
          ((f - p.1 : ℕ) : K) * fgCoeff p.2 * Gz w (fgIdx (p.1 : ℤ) (d : ℤ) p.2) :=
        (Finset.sum_product' (Finset.Ico 1 f) (Finset.range 3)
          (fun j t => ((f - j : ℕ) : K) * fgCoeff t * Gz w (fgIdx (j : ℤ) (d : ℤ) t))).symm

theorem Gz_mul_xCoeff_eq_row (w : K) (hw : w ≠ 0) (d n : ℕ) :
    Gz w (d : ℤ) * xCoeff w n
      = ∑ p ∈ n.divisors ×ˢ Finset.range 3,
          (p.1 : K) * fgCoeff p.2 * Gz w (fgIdx (p.1 : ℤ) (d : ℤ) p.2) :=
  calc Gz w (d : ℤ) * xCoeff w n
      = ∑ f ∈ n.divisors, Gz w (d : ℤ) * ((f : K) * Fz w (f : ℤ)) := by
        rw [xCoeff_eq_divisorSum_Fz, Finset.mul_sum]
    _ = ∑ f ∈ n.divisors, ∑ t ∈ Finset.range 3,
          (f : K) * fgCoeff t * Gz w (fgIdx (f : ℤ) (d : ℤ) t) := by
        refine Finset.sum_congr rfl fun f _ => ?_
        calc Gz w (d : ℤ) * ((f : K) * Fz w (f : ℤ))
            = (f : K) * (Fz w (f : ℤ) * Gz w (d : ℤ)) := by ring
          _ = (f : K) * ∑ t ∈ Finset.range 3,
                fgCoeff t * Gz w (fgIdx (f : ℤ) (d : ℤ) t) := by
              rw [Fz_mul_Gz_eq_row hw (f : ℤ) (d : ℤ)]
          _ = ∑ t ∈ Finset.range 3,
                (f : K) * (fgCoeff t * Gz w (fgIdx (f : ℤ) (d : ℤ) t)) := by
              rw [Finset.mul_sum]
          _ = ∑ t ∈ Finset.range 3,
                (f : K) * fgCoeff t * Gz w (fgIdx (f : ℤ) (d : ℤ) t) :=
              Finset.sum_congr rfl fun t _ => by ring
    _ = ∑ p ∈ n.divisors ×ˢ Finset.range 3,
          (p.1 : K) * fgCoeff p.2 * Gz w (fgIdx (p.1 : ℤ) (d : ℤ) p.2) :=
        (Finset.sum_product' n.divisors (Finset.range 3)
          (fun f t => (f : K) * fgCoeff t * Gz w (fgIdx (f : ℤ) (d : ℤ) t))).symm

theorem le_of_mem_divisors' {d n : ℕ} (hd : d ∈ n.divisors) : d ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.mem_divisors.mp hd).1

end RowReadings
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

section CrossInteriorBlock

def crossInteriorIdx (M : ℕ) : Finset (Σ _ : (Σ _ : ℕ, ℕ), Σ _ : (Σ _ : ℕ, ℕ), ℕ) :=
  ((Finset.Ico 1 M).sigma fun b => b.divisors).sigma fun p => psiBlockIdx (M - p.1)

theorem bounds_of_mem_crossInteriorIdx {M : ℕ}
    {y : Σ _ : (Σ _ : ℕ, ℕ), Σ _ : (Σ _ : ℕ, ℕ), ℕ} (hy : y ∈ crossInteriorIdx M) :
    1 ≤ y.1.2 ∧ 1 ≤ y.2.1.2 ∧ 1 ≤ y.2.2 ∧ y.1.2 + y.2.1.2 + y.2.2 ≤ M := by
  have h1 := Finset.mem_sigma.mp hy
  have h2 := Finset.mem_sigma.mp h1.1
  have hb : 1 ≤ y.1.1 ∧ y.1.1 < M := Finset.mem_Ico.mp h2.1
  have hd1 : 1 ≤ y.1.2 := Nat.pos_of_mem_divisors h2.2
  have hdb : y.1.2 ≤ y.1.1 := le_of_mem_divisors' h2.2
  have hef : y.2.1.2 + y.2.2 ≤ M - y.1.1 := add_le_of_mem_psiBlockIdx h1.2
  have he1 : 1 ≤ y.2.1.2 := (bounds_of_mem_psiBlockIdx h1.2).1
  have hf1 : 1 ≤ y.2.2 := (bounds_of_mem_psiBlockIdx h1.2).2.2.1
  exact ⟨hd1, he1, hf1, by omega⟩

theorem sum_crossInteriorNest_eq_sigma {β : Type*} [AddCommMonoid β] (M : ℕ)
    (F : ℕ → ℕ → ℕ → ℕ → ℕ → β) :
    ∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ c ∈ Finset.Ico 1 (M - b), ∑ e ∈ c.divisors,
        ∑ f ∈ (M - b - c).divisors, F b d c e f
      = ∑ y ∈ crossInteriorIdx M, F y.1.1 y.1.2 y.2.1.1 y.2.1.2 y.2.2 :=
  calc ∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ c ∈ Finset.Ico 1 (M - b), ∑ e ∈ c.divisors,
          ∑ f ∈ (M - b - c).divisors, F b d c e f
      = ∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors,
          ∑ x ∈ psiBlockIdx (M - b), F b d x.1.1 x.1.2 x.2 :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
          sum_nest3_eq_sigma (Finset.Ico 1 (M - b)) (fun c => c.divisors)
            (fun c _ => (M - b - c).divisors) (F b d)
    _ = ∑ p ∈ (Finset.Ico 1 M).sigma (fun b => b.divisors),
          ∑ x ∈ psiBlockIdx (M - p.1), F p.1 p.2 x.1.1 x.1.2 x.2 :=
        Finset.sum_sigma' (Finset.Ico 1 M) (fun b => b.divisors)
          (fun b d => ∑ x ∈ psiBlockIdx (M - b), F b d x.1.1 x.1.2 x.2)
    _ = ∑ y ∈ crossInteriorIdx M, F y.1.1 y.1.2 y.2.1.1 y.2.1.2 y.2.2 :=
        Finset.sum_sigma' ((Finset.Ico 1 M).sigma fun b => b.divisors)
          (fun p => psiBlockIdx (M - p.1))
          (fun p x => F p.1 p.2 x.1.1 x.1.2 x.2)

theorem hasCanonicalTable_crossInteriorBlock :
    HasCanonicalTable K fun u v M =>
      ∑ b ∈ Finset.Ico 1 M, (∑ d ∈ b.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
        * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
            (fun i => xCoeffFull u i - xCoeffFull v i) (M - b) := by

  have hd_le : ∀ (M : ℕ), ∀ y ∈ crossInteriorIdx M, ((y.1.2 : ℤ)).natAbs ≤ M := fun M y hy => by
    have h := bounds_of_mem_crossInteriorIdx hy
    simpa using (by omega : y.1.2 ≤ M)
  have hffg_le : ∀ (M : ℕ), ∀ y ∈ crossInteriorIdx M, ∀ t ∈ Finset.range 9,
      (ffgIdx (y.2.1.2 : ℤ) (y.2.2 : ℤ) (y.1.2 : ℤ) t).natAbs ≤ M := fun M y hy t _ => by
    have h := bounds_of_mem_crossInteriorIdx hy
    exact natAbs_ffgIdx_le (by simp only [Int.natAbs_natCast]; omega) t
  have hfg_e_le : ∀ (M : ℕ), ∀ y ∈ crossInteriorIdx M, ∀ t ∈ Finset.range 3,
      (fgIdx (y.2.1.2 : ℤ) (y.1.2 : ℤ) t).natAbs ≤ M := fun M y hy t _ => by
    have h := bounds_of_mem_crossInteriorIdx hy
    exact natAbs_fgIdx_le (by simp only [Int.natAbs_natCast]; omega) t
  have hfg_f_le : ∀ (M : ℕ), ∀ y ∈ crossInteriorIdx M, ∀ t ∈ Finset.range 3,
      (fgIdx (y.2.2 : ℤ) (y.1.2 : ℤ) t).natAbs ≤ M := fun M y hy t _ => by
    have h := bounds_of_mem_crossInteriorIdx hy
    exact natAbs_fgIdx_le (by simp only [Int.natAbs_natCast]; omega) t
  have hcdef : ∀ (y : Σ _ : (Σ _ : ℕ, ℕ), Σ _ : (Σ _ : ℕ, ℕ), ℕ),
      ‖(y.1.2 : K) * (y.2.1.2 : K) * (y.2.2 : K)‖ ≤ 1 := fun y =>
    norm_mul_le_one (norm_mul_le_one (norm_natCast_le_one K _) (norm_natCast_le_one K _))
      (norm_natCast_le_one K _)
  have hone : ‖(1 : K)‖ ≤ 1 := by simp

  have h1 : HasCanonicalTable K fun u v M => ∑ y ∈ crossInteriorIdx M,
      ((y.1.2 : K) * (y.2.1.2 : K) * (y.2.2 : K))
        * (∑ t ∈ Finset.range 9,
            ffgCoeff t * Gz u (ffgIdx (y.2.1.2 : ℤ) (y.2.2 : ℤ) (y.1.2 : ℤ) t))
        * (∑ t ∈ Finset.range 1, (1 : K) * Gz v (y.1.2 : ℤ)) :=
    hasCanonicalTable_of_rows (fun M => crossInteriorIdx M)
      (fun _ y => (y.1.2 : K) * (y.2.1.2 : K) * (y.2.2 : K))
      (fun _ _ => Finset.range 9) (fun _ _ t => ffgCoeff t)
      (fun _ y t => ffgIdx (y.2.1.2 : ℤ) (y.2.2 : ℤ) (y.1.2 : ℤ) t)
      (fun _ _ => Finset.range 1) (fun _ _ _ => (1 : K)) (fun _ y _ => (y.1.2 : ℤ))
      hffg_le (fun M y hy t _ => hd_le M y hy)
      (fun M y hy i _ j _ => norm_mul_le_one (norm_mul_le_one (hcdef y)
        (norm_ffgCoeff_le_one i)) hone)
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)

  have h2 : HasCanonicalTable K fun u v M => ∑ y ∈ crossInteriorIdx M,
      ((y.1.2 : K) * (y.2.1.2 : K) * (y.2.2 : K))
        * (∑ t ∈ Finset.range 3, fgCoeff t * Gz u (fgIdx (y.2.1.2 : ℤ) (y.1.2 : ℤ) t))
        * (∑ t ∈ Finset.range 3, fgCoeff t * Gz v (fgIdx (y.2.2 : ℤ) (y.1.2 : ℤ) t)) :=
    hasCanonicalTable_of_rows (fun M => crossInteriorIdx M)
      (fun _ y => (y.1.2 : K) * (y.2.1.2 : K) * (y.2.2 : K))
      (fun _ _ => Finset.range 3) (fun _ _ t => fgCoeff t)
      (fun _ y t => fgIdx (y.2.1.2 : ℤ) (y.1.2 : ℤ) t)
      (fun _ _ => Finset.range 3) (fun _ _ t => fgCoeff t)
      (fun _ y t => fgIdx (y.2.2 : ℤ) (y.1.2 : ℤ) t)
      hfg_e_le hfg_f_le
      (fun M y hy i _ j _ => norm_mul_le_one (norm_mul_le_one (hcdef y)
        (norm_fgCoeff_le_one i)) (norm_fgCoeff_le_one j))
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)

  have h3 : HasCanonicalTable K fun u v M => ∑ y ∈ crossInteriorIdx M,
      ((y.1.2 : K) * (y.2.1.2 : K) * (y.2.2 : K))
        * (∑ t ∈ Finset.range 3, fgCoeff t * Gz u (fgIdx (y.2.2 : ℤ) (y.1.2 : ℤ) t))
        * (∑ t ∈ Finset.range 3, fgCoeff t * Gz v (fgIdx (y.2.1.2 : ℤ) (y.1.2 : ℤ) t)) :=
    hasCanonicalTable_of_rows (fun M => crossInteriorIdx M)
      (fun _ y => (y.1.2 : K) * (y.2.1.2 : K) * (y.2.2 : K))
      (fun _ _ => Finset.range 3) (fun _ _ t => fgCoeff t)
      (fun _ y t => fgIdx (y.2.2 : ℤ) (y.1.2 : ℤ) t)
      (fun _ _ => Finset.range 3) (fun _ _ t => fgCoeff t)
      (fun _ y t => fgIdx (y.2.1.2 : ℤ) (y.1.2 : ℤ) t)
      hfg_f_le hfg_e_le
      (fun M y hy i _ j _ => norm_mul_le_one (norm_mul_le_one (hcdef y)
        (norm_fgCoeff_le_one i)) (norm_fgCoeff_le_one j))
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)

  have h4 : HasCanonicalTable K fun u v M => ∑ y ∈ crossInteriorIdx M,
      ((y.1.2 : K) * (y.2.1.2 : K) * (y.2.2 : K))
        * (∑ t ∈ Finset.range 1, (1 : K) * Gz u (y.1.2 : ℤ))
        * (∑ t ∈ Finset.range 9,
            ffgCoeff t * Gz v (ffgIdx (y.2.1.2 : ℤ) (y.2.2 : ℤ) (y.1.2 : ℤ) t)) :=
    hasCanonicalTable_of_rows (fun M => crossInteriorIdx M)
      (fun _ y => (y.1.2 : K) * (y.2.1.2 : K) * (y.2.2 : K))
      (fun _ _ => Finset.range 1) (fun _ _ _ => (1 : K)) (fun _ y _ => (y.1.2 : ℤ))
      (fun _ _ => Finset.range 9) (fun _ _ t => ffgCoeff t)
      (fun _ y t => ffgIdx (y.2.1.2 : ℤ) (y.2.2 : ℤ) (y.1.2 : ℤ) t)
      (fun M y hy t _ => hd_le M y hy) hffg_le
      (fun M y hy i _ j _ => norm_mul_le_one (norm_mul_le_one (hcdef y) hone)
        (norm_ffgCoeff_le_one j))
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)
  refine (((h1.sub h2).sub h3).add h4).congr ?_
  intro u v hu hv hu1 hv1 hm hd M hM
  beta_reduce
  rw [crossInterior_block_eq_rows hu hv M, sum_crossInteriorNest_eq_sigma,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  beta_reduce
  rw [ffgRow_eval hu (y.2.1.2 : ℤ) (y.2.2 : ℤ) (y.1.2 : ℤ),
    ffgRow_eval hv (y.2.1.2 : ℤ) (y.2.2 : ℤ) (y.1.2 : ℤ),
    fgRow_eval hu (y.2.1.2 : ℤ) (y.1.2 : ℤ), fgRow_eval hu (y.2.2 : ℤ) (y.1.2 : ℤ),
    fgRow_eval hv (y.2.1.2 : ℤ) (y.1.2 : ℤ), fgRow_eval hv (y.2.2 : ℤ) (y.1.2 : ℤ)]
  simp only [Finset.sum_range_one]
  ring

end CrossInteriorBlock
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

section SvComplex

def sv1Idx (M : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (M.divisors).sigma fun e => Finset.range e

theorem bounds_of_mem_sv1Idx {M : ℕ} {p : Σ _ : ℕ, ℕ} (hp : p ∈ sv1Idx M) :
    p.2 < p.1 ∧ p.1 ≤ M := by
  have h1 := Finset.mem_sigma.mp hp
  exact ⟨Finset.mem_range.mp h1.2, le_of_mem_divisors' h1.1⟩

theorem hasCanonicalTable_svBlock1 :
    HasCanonicalTable K fun u v M => ∑ e ∈ M.divisors, 2 * (e : K)
      * (∑ i ∈ Finset.range e,
          ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j))
              * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j))
            - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2),
                  tent u (e - 1 - i - 1 - 2 * j))
              * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j)))) := by
  have hcoeff : ∀ (n k : ℕ), ‖((n : K)) - (k : K)‖ ≤ 1 := fun n k =>
    norm_sub_le_one (norm_natCast_le_one K n) (norm_natCast_le_one K k)
  have hc2 : ∀ (e : ℕ), ‖(2 : K) * (e : K)‖ ≤ 1 := fun e =>
    norm_mul_le_one norm_two_le_one (norm_natCast_le_one K e)

  have h1a : HasCanonicalTable K fun u v M => ∑ p ∈ sv1Idx M, (2 * (p.1 : K))
      * (∑ k ∈ Finset.Ico 1 (p.2 + 1), (((p.2 + 1 : ℕ) : K) - (k : K)) * Gz u (k : ℤ))
      * (∑ k ∈ Finset.Ico 1 (p.1 - p.2), (((p.1 - p.2 : ℕ) : K) - (k : K)) * Gz v (k : ℤ)) :=
    hasCanonicalTable_of_rows (fun M => sv1Idx M) (fun _ p => 2 * (p.1 : K))
      (fun _ p => Finset.Ico 1 (p.2 + 1)) (fun _ p k => ((p.2 + 1 : ℕ) : K) - (k : K))
      (fun _ _ k => (k : ℤ))
      (fun _ p => Finset.Ico 1 (p.1 - p.2)) (fun _ p k => ((p.1 - p.2 : ℕ) : K) - (k : K))
      (fun _ _ k => (k : ℤ))
      (fun M p hp k hk => by
        have h1 := bounds_of_mem_sv1Idx hp
        have h2 := (Finset.mem_Ico.mp hk).2
        simpa using (by omega : k ≤ M))
      (fun M p hp k hk => by
        have h1 := bounds_of_mem_sv1Idx hp
        have h2 := (Finset.mem_Ico.mp hk).2
        simpa using (by omega : k ≤ M))
      (fun M p _ k _ k' _ => norm_mul_le_one (norm_mul_le_one (hc2 p.1) (hcoeff _ k))
        (hcoeff _ k'))
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)

  have h1b : HasCanonicalTable K fun u v M => ∑ p ∈ sv1Idx M, (2 * (p.1 : K))
      * (∑ k ∈ Finset.Ico 1 (p.1 - 1 - p.2),
          (((p.1 - 1 - p.2 : ℕ) : K) - (k : K)) * Gz u (k : ℤ))
      * (∑ k ∈ Finset.Ico 1 p.2, (((p.2 : ℕ) : K) - (k : K)) * Gz v (k : ℤ)) :=
    hasCanonicalTable_of_rows (fun M => sv1Idx M) (fun _ p => 2 * (p.1 : K))
      (fun _ p => Finset.Ico 1 (p.1 - 1 - p.2))
      (fun _ p k => ((p.1 - 1 - p.2 : ℕ) : K) - (k : K)) (fun _ _ k => (k : ℤ))
      (fun _ p => Finset.Ico 1 p.2) (fun _ p k => ((p.2 : ℕ) : K) - (k : K))
      (fun _ _ k => (k : ℤ))
      (fun M p hp k hk => by
        have h1 := bounds_of_mem_sv1Idx hp
        have h2 := (Finset.mem_Ico.mp hk).2
        simpa using (by omega : k ≤ M))
      (fun M p hp k hk => by
        have h1 := bounds_of_mem_sv1Idx hp
        have h2 := (Finset.mem_Ico.mp hk).2
        simpa using (by omega : k ≤ M))
      (fun M p _ k _ k' _ => norm_mul_le_one (norm_mul_le_one (hc2 p.1) (hcoeff _ k))
        (hcoeff _ k'))
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)
  refine (h1a.sub h1b).congr ?_
  intro u v hu hv hu1 hv1 hm hd M hM
  beta_reduce
  rw [← Finset.sum_sub_distrib]
  refine Eq.symm ?_
  calc ∑ e ∈ M.divisors, 2 * (e : K)
        * (∑ i ∈ Finset.range e,
            ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j))
                * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j))
              - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2),
                    tent u (e - 1 - i - 1 - 2 * j))
                * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j))))
      = ∑ e ∈ M.divisors, ∑ i ∈ Finset.range e,
          (2 * (e : K)
              * (∑ k ∈ Finset.Ico 1 (i + 1), (((i + 1 : ℕ) : K) - (k : K)) * Gz u (k : ℤ))
              * (∑ k ∈ Finset.Ico 1 (e - i), (((e - i : ℕ) : K) - (k : K)) * Gz v (k : ℤ))
            - 2 * (e : K)
              * (∑ k ∈ Finset.Ico 1 (e - 1 - i),
                  (((e - 1 - i : ℕ) : K) - (k : K)) * Gz u (k : ℤ))
              * (∑ k ∈ Finset.Ico 1 i, (((i : ℕ) : K) - (k : K)) * Gz v (k : ℤ))) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Gz_one_mul_telescope_succ_eq_sum u hu i,
          Gz_one_mul_telescope_eq_sum v hv (e - i),
          Gz_one_mul_telescope_eq_sum u hu (e - 1 - i),
          Gz_one_mul_telescope_eq_sum v hv i]
        ring
    _ = ∑ p ∈ sv1Idx M,
          (2 * (p.1 : K)
              * (∑ k ∈ Finset.Ico 1 (p.2 + 1), (((p.2 + 1 : ℕ) : K) - (k : K)) * Gz u (k : ℤ))
              * (∑ k ∈ Finset.Ico 1 (p.1 - p.2),
                  (((p.1 - p.2 : ℕ) : K) - (k : K)) * Gz v (k : ℤ))
            - 2 * (p.1 : K)
              * (∑ k ∈ Finset.Ico 1 (p.1 - 1 - p.2),
                  (((p.1 - 1 - p.2 : ℕ) : K) - (k : K)) * Gz u (k : ℤ))
              * (∑ k ∈ Finset.Ico 1 p.2, (((p.2 : ℕ) : K) - (k : K)) * Gz v (k : ℤ))) :=
        Finset.sum_sigma' _ _ _

theorem hasCanonicalTable_svBlock2 :
    HasCanonicalTable K fun u v M => ∑ d ∈ M.divisors, 2 * (d : K)
      * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
          * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))) :=
  hasCanonicalTable_of_rows (fun M => M.divisors) (fun _ d => 2 * (d : K))
    (fun _ d => Finset.Ico 1 d) (fun _ d k => ((d : K)) - (k : K)) (fun _ _ k => (k : ℤ))
    (fun _ d => Finset.Ico 1 d) (fun _ d k => ((d : K)) - (k : K)) (fun _ _ k => (k : ℤ))
    (fun M d hd k hk => by
      have h1 := (Finset.mem_Ico.mp hk).2
      have h2 := le_of_mem_divisors' hd
      simpa using (by omega : k ≤ M))
    (fun M d hd k hk => by
      have h1 := (Finset.mem_Ico.mp hk).2
      have h2 := le_of_mem_divisors' hd
      simpa using (by omega : k ≤ M))
    (fun M d _ k _ k' _ => norm_mul_le_one (norm_mul_le_one
      (norm_mul_le_one norm_two_le_one (norm_natCast_le_one K _))
      (norm_sub_le_one (norm_natCast_le_one K _) (norm_natCast_le_one K _)))
      (norm_sub_le_one (norm_natCast_le_one K _) (norm_natCast_le_one K _)))
    (fun u v hu hv _ _ _ _ M _ => by
      beta_reduce
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Gz_one_mul_telescope_eq_sum u hu d, Gz_one_mul_telescope_eq_sum v hv d]
      ring)

theorem hasCanonicalTable_svBlock3 :
    HasCanonicalTable K fun u v M => ∑ d ∈ M.divisors, (d : K)
      * (Gz v (d : ℤ)
            * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K))
                * (Gz u 1 * ∑ j ∈ Finset.range (i / 2), tent u (i - 1 - 2 * j)))
        + Gz u (d : ℤ)
            * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K))
                * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j)))) := by
  have hsig : ∀ (M d : ℕ), d ∈ M.divisors →
      ∀ p ∈ (Finset.Ico 1 d).sigma (fun i => Finset.Ico 1 i), ((p.2 : ℤ)).natAbs ≤ M :=
    fun M d hd p hp => by
      have h1 := Finset.mem_sigma.mp hp
      have h2 := (Finset.mem_Ico.mp h1.1).2
      have h3 := (Finset.mem_Ico.mp h1.2).2
      have h4 := le_of_mem_divisors' hd
      simpa using (by omega : p.2 ≤ M)
  have hdle : ∀ (M d : ℕ), d ∈ M.divisors → ((d : ℤ)).natAbs ≤ M := fun M d hd => by
    simpa using le_of_mem_divisors' hd
  have hAcoeff : ∀ (d : ℕ) (p : Σ _ : ℕ, ℕ),
      ‖((d : K) - (p.1 : K)) * ((p.1 : K) - (p.2 : K))‖ ≤ 1 := fun d p =>
    norm_mul_le_one (norm_sub_le_one (norm_natCast_le_one K _) (norm_natCast_le_one K _))
      (norm_sub_le_one (norm_natCast_le_one K _) (norm_natCast_le_one K _))

  have h3a : HasCanonicalTable K fun u v M => ∑ d ∈ M.divisors, (d : K)
      * (∑ p ∈ (Finset.Ico 1 d).sigma (fun i => Finset.Ico 1 i),
          ((d : K) - (p.1 : K)) * ((p.1 : K) - (p.2 : K)) * Gz u (p.2 : ℤ))
      * (∑ t ∈ Finset.range 1, (1 : K) * Gz v (d : ℤ)) :=
    hasCanonicalTable_of_rows (fun M => M.divisors) (fun _ d => (d : K))
      (fun _ d => (Finset.Ico 1 d).sigma (fun i => Finset.Ico 1 i))
      (fun _ d p => ((d : K) - (p.1 : K)) * ((p.1 : K) - (p.2 : K))) (fun _ _ p => (p.2 : ℤ))
      (fun _ _ => Finset.range 1) (fun _ _ _ => (1 : K)) (fun _ d _ => (d : ℤ))
      hsig (fun M d hd t _ => hdle M d hd)
      (fun M d _ p _ t _ => norm_mul_le_one (norm_mul_le_one (norm_natCast_le_one K _)
        (hAcoeff d p)) norm_one.le)
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)

  have h3b : HasCanonicalTable K fun u v M => ∑ d ∈ M.divisors, (d : K)
      * (∑ t ∈ Finset.range 1, (1 : K) * Gz u (d : ℤ))
      * (∑ p ∈ (Finset.Ico 1 d).sigma (fun i => Finset.Ico 1 i),
          ((d : K) - (p.1 : K)) * ((p.1 : K) - (p.2 : K)) * Gz v (p.2 : ℤ)) :=
    hasCanonicalTable_of_rows (fun M => M.divisors) (fun _ d => (d : K))
      (fun _ _ => Finset.range 1) (fun _ _ _ => (1 : K)) (fun _ d _ => (d : ℤ))
      (fun _ d => (Finset.Ico 1 d).sigma (fun i => Finset.Ico 1 i))
      (fun _ d p => ((d : K) - (p.1 : K)) * ((p.1 : K) - (p.2 : K))) (fun _ _ p => (p.2 : ℤ))
      (fun M d hd t _ => hdle M d hd) hsig
      (fun M d _ t _ p _ => norm_mul_le_one (norm_mul_le_one (norm_natCast_le_one K _)
        norm_one.le) (hAcoeff d p))
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)
  refine (h3a.add h3b).congr ?_
  intro u v hu hv hu1 hv1 hm hd M hM
  beta_reduce
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [aColumn_eq_row u hu d, aColumn_eq_row v hv d]
  simp only [Finset.sum_range_one]
  ring

theorem hasCanonicalTable_svBlock4 [CharZero K] :
    HasCanonicalTable K fun u v M => ∑ a ∈ Finset.Ico 1 M,
      (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
        * (2 * ∑ f ∈ (M - a).divisors, (f : K) * (tent u f + tent v f)) := by
  have hd_le : ∀ (M : ℕ), ∀ x ∈ psiBlockIdx M, ((x.1.2 : ℤ)).natAbs ≤ M := fun M x hx => by
    simpa using (bounds_of_mem_psiBlockIdx hx).2.1
  have hfg_le : ∀ (M : ℕ), ∀ x ∈ psiBlockIdx M, ∀ p ∈ Finset.Ico 1 x.2 ×ˢ Finset.range 3,
      (fgIdx (p.1 : ℤ) (x.1.2 : ℤ) p.2).natAbs ≤ M := fun M x hx p hp => by
    have h1 := (Finset.mem_product.mp hp).1
    have h2 := (Finset.mem_Ico.mp h1).2
    have h3 := add_le_of_mem_psiBlockIdx hx
    exact natAbs_fgIdx_le (by simp only [Int.natAbs_natCast]; omega) p.2
  have h4K : ‖(4 : K)‖ ≤ 1 := by simpa using norm_natCast_le_one K 4
  have hdf : ∀ (x : Σ _ : (Σ _ : ℕ, ℕ), ℕ), ‖(2 : K) * (x.1.2 : K) * (x.2 : K)‖ ≤ 1 := fun x =>
    norm_mul_le_one (norm_mul_le_one norm_two_le_one (norm_natCast_le_one K _))
      (norm_natCast_le_one K _)
  have htcoeff : ∀ (n k : ℕ) (t : ℕ), ‖(((n - k : ℕ)) : K) * fgCoeff t‖ ≤ 1 := fun n k t =>
    norm_mul_le_one (norm_natCast_le_one K _) (norm_fgCoeff_le_one t)

  have h4a : HasCanonicalTable K fun u v M => ∑ x ∈ psiBlockIdx M,
      ((4 : K) * (x.1.2 : K) * (x.2 : K) ^ 3) * Gz u (x.1.2 : ℤ) * Gz v (x.1.2 : ℤ) :=
    hasCanonicalTable_of_atoms (fun M => psiBlockIdx M)
      (fun _ x => (4 : K) * (x.1.2 : K) * (x.2 : K) ^ 3)
      (fun _ x => (x.1.2 : ℤ)) (fun _ x => (x.1.2 : ℤ))
      hd_le hd_le
      (fun M x _ => norm_mul_le_one (norm_mul_le_one h4K (norm_natCast_le_one K _))
        (norm_pow_le_one (norm_natCast_le_one K _) 3))
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)

  have h4b : HasCanonicalTable K fun u v M => ∑ x ∈ psiBlockIdx M,
      (2 * (x.1.2 : K) * (x.2 : K))
        * (∑ p ∈ Finset.Ico 1 x.2 ×ˢ Finset.range 3,
            ((x.2 - p.1 : ℕ) : K) * fgCoeff p.2 * Gz u (fgIdx (p.1 : ℤ) (x.1.2 : ℤ) p.2))
        * (∑ t ∈ Finset.range 1, (1 : K) * Gz v (x.1.2 : ℤ)) :=
    hasCanonicalTable_of_rows (fun M => psiBlockIdx M)
      (fun _ x => 2 * (x.1.2 : K) * (x.2 : K))
      (fun _ x => Finset.Ico 1 x.2 ×ˢ Finset.range 3)
      (fun _ x p => ((x.2 - p.1 : ℕ) : K) * fgCoeff p.2)
      (fun _ x p => fgIdx (p.1 : ℤ) (x.1.2 : ℤ) p.2)
      (fun _ _ => Finset.range 1) (fun _ _ _ => (1 : K)) (fun _ x _ => (x.1.2 : ℤ))
      hfg_le (fun M x hx t _ => hd_le M x hx)
      (fun M x _ p _ t _ => norm_mul_le_one (norm_mul_le_one (hdf x) (htcoeff x.2 p.1 p.2))
        norm_one.le)
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)

  have h4c : HasCanonicalTable K fun u v M => ∑ x ∈ psiBlockIdx M,
      (2 * (x.1.2 : K) * (x.2 : K))
        * (∑ t ∈ Finset.range 1, (1 : K) * Gz u (x.1.2 : ℤ))
        * (∑ p ∈ Finset.Ico 1 x.2 ×ˢ Finset.range 3,
            ((x.2 - p.1 : ℕ) : K) * fgCoeff p.2 * Gz v (fgIdx (p.1 : ℤ) (x.1.2 : ℤ) p.2)) :=
    hasCanonicalTable_of_rows (fun M => psiBlockIdx M)
      (fun _ x => 2 * (x.1.2 : K) * (x.2 : K))
      (fun _ _ => Finset.range 1) (fun _ _ _ => (1 : K)) (fun _ x _ => (x.1.2 : ℤ))
      (fun _ x => Finset.Ico 1 x.2 ×ˢ Finset.range 3)
      (fun _ x p => ((x.2 - p.1 : ℕ) : K) * fgCoeff p.2)
      (fun _ x p => fgIdx (p.1 : ℤ) (x.1.2 : ℤ) p.2)
      (fun M x hx t _ => hd_le M x hx) hfg_le
      (fun M x _ t _ p _ => norm_mul_le_one (norm_mul_le_one (hdf x) norm_one.le)
        (htcoeff x.2 p.1 p.2))
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)
  refine ((h4a.add h4b).add h4c).congr ?_
  intro u v hu hv hu1 hv1 hm hd M hM
  beta_reduce
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Eq.symm ?_
  calc ∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
          * (2 * ∑ f ∈ (M - a).divisors, (f : K) * (tent u f + tent v f))
      = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ f ∈ (M - a).divisors,
          ((d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (2 * ((f : K) * (tent u f + tent v f))) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = ∑ x ∈ psiBlockIdx M,
          ((x.1.2 : K) * (Gz u (x.1.2 : ℤ) * Gz v (x.1.2 : ℤ)))
            * (2 * ((x.2 : K) * (tent u x.2 + tent v x.2))) :=
        sum_nest3_eq_sigma _ _ _ _
    _ = ∑ x ∈ psiBlockIdx M,
          (((4 : K) * (x.1.2 : K) * (x.2 : K) ^ 3) * Gz u (x.1.2 : ℤ) * Gz v (x.1.2 : ℤ)
            + (2 * (x.1.2 : K) * (x.2 : K))
              * (∑ p ∈ Finset.Ico 1 x.2 ×ˢ Finset.range 3,
                  ((x.2 - p.1 : ℕ) : K) * fgCoeff p.2 * Gz u (fgIdx (p.1 : ℤ) (x.1.2 : ℤ) p.2))
              * (∑ t ∈ Finset.range 1, (1 : K) * Gz v (x.1.2 : ℤ))
            + (2 * (x.1.2 : K) * (x.2 : K))
              * (∑ t ∈ Finset.range 1, (1 : K) * Gz u (x.1.2 : ℤ))
              * (∑ p ∈ Finset.Ico 1 x.2 ×ˢ Finset.range 3,
                  ((x.2 - p.1 : ℕ) : K) * fgCoeff p.2
                    * Gz v (fgIdx (p.1 : ℤ) (x.1.2 : ℤ) p.2))) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [tent_eq_sq_add_sum_Ico hu hu1 x.2, tent_eq_sq_add_sum_Ico hv hv1 x.2,
          ← Gz_mul_tentTail_eq_row u hu x.1.2 x.2, ← Gz_mul_tentTail_eq_row v hv x.1.2 x.2]
        simp only [Finset.sum_range_one]
        ring

theorem hasCanonicalTable_svBlock5 :
    HasCanonicalTable K fun u v M => ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, 2 * (d : K)
      * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
            * (Gz v (d : ℤ) * xCoeff v (M - a))
        + (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))
            * (Gz u (d : ℤ) * xCoeff u (M - a))) := by
  have hk_le : ∀ (M : ℕ), ∀ x ∈ (Finset.Ico 1 M).sigma (fun a => a.divisors),
      ∀ k ∈ Finset.Ico 1 x.2, ((k : ℤ)).natAbs ≤ M := fun M x hx k hk => by
    have h1 := Finset.mem_sigma.mp hx
    have h2 := (Finset.mem_Ico.mp h1.1).2
    have h3 := le_of_mem_divisors' h1.2
    have h4 := (Finset.mem_Ico.mp hk).2
    simpa using (by omega : k ≤ M)
  have hfg_le : ∀ (M : ℕ), ∀ x ∈ (Finset.Ico 1 M).sigma (fun a => a.divisors),
      ∀ p ∈ (M - x.1).divisors ×ˢ Finset.range 3,
      (fgIdx (p.1 : ℤ) (x.2 : ℤ) p.2).natAbs ≤ M := fun M x hx p hp => by
    have h1 := Finset.mem_sigma.mp hx
    have h2 := (Finset.mem_Ico.mp h1.1).2
    have h3 := le_of_mem_divisors' h1.2
    have h4 := le_of_mem_divisors' (Finset.mem_product.mp hp).1
    exact natAbs_fgIdx_le (by simp only [Int.natAbs_natCast]; omega) p.2
  have htel : ∀ (d k : ℕ), ‖((d : K)) - (k : K)‖ ≤ 1 := fun d k =>
    norm_sub_le_one (norm_natCast_le_one K d) (norm_natCast_le_one K k)
  have hxc : ∀ (f t : ℕ), ‖(f : K) * fgCoeff t‖ ≤ 1 := fun f t =>
    norm_mul_le_one (norm_natCast_le_one K f) (norm_fgCoeff_le_one t)
  have h2d : ∀ (d : ℕ), ‖(2 : K) * (d : K)‖ ≤ 1 := fun d =>
    norm_mul_le_one norm_two_le_one (norm_natCast_le_one K d)

  have h5a : HasCanonicalTable K fun u v M =>
      ∑ x ∈ (Finset.Ico 1 M).sigma (fun a => a.divisors), (2 * (x.2 : K))
        * (∑ k ∈ Finset.Ico 1 x.2, ((x.2 : K) - (k : K)) * Gz u (k : ℤ))
        * (∑ p ∈ (M - x.1).divisors ×ˢ Finset.range 3,
            (p.1 : K) * fgCoeff p.2 * Gz v (fgIdx (p.1 : ℤ) (x.2 : ℤ) p.2)) :=
    hasCanonicalTable_of_rows (fun M => (Finset.Ico 1 M).sigma (fun a => a.divisors))
      (fun _ x => 2 * (x.2 : K))
      (fun _ x => Finset.Ico 1 x.2) (fun _ x k => ((x.2 : K)) - (k : K))
      (fun _ _ k => (k : ℤ))
      (fun M x => (M - x.1).divisors ×ˢ Finset.range 3)
      (fun _ _ p => (p.1 : K) * fgCoeff p.2)
      (fun _ x p => fgIdx (p.1 : ℤ) (x.2 : ℤ) p.2)
      hk_le hfg_le
      (fun M x _ k _ p _ => norm_mul_le_one (norm_mul_le_one (h2d x.2) (htel x.2 k))
        (hxc p.1 p.2))
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)

  have h5b : HasCanonicalTable K fun u v M =>
      ∑ x ∈ (Finset.Ico 1 M).sigma (fun a => a.divisors), (2 * (x.2 : K))
        * (∑ p ∈ (M - x.1).divisors ×ˢ Finset.range 3,
            (p.1 : K) * fgCoeff p.2 * Gz u (fgIdx (p.1 : ℤ) (x.2 : ℤ) p.2))
        * (∑ k ∈ Finset.Ico 1 x.2, ((x.2 : K) - (k : K)) * Gz v (k : ℤ)) :=
    hasCanonicalTable_of_rows (fun M => (Finset.Ico 1 M).sigma (fun a => a.divisors))
      (fun _ x => 2 * (x.2 : K))
      (fun M x => (M - x.1).divisors ×ˢ Finset.range 3)
      (fun _ _ p => (p.1 : K) * fgCoeff p.2)
      (fun _ x p => fgIdx (p.1 : ℤ) (x.2 : ℤ) p.2)
      (fun _ x => Finset.Ico 1 x.2) (fun _ x k => ((x.2 : K)) - (k : K))
      (fun _ _ k => (k : ℤ))
      hfg_le hk_le
      (fun M x _ p _ k _ => norm_mul_le_one (norm_mul_le_one (h2d x.2) (hxc p.1 p.2))
        (htel x.2 k))
      (fun _ _ _ _ _ _ _ _ _ _ => rfl)
  refine (h5a.add h5b).congr ?_
  intro u v hu hv hu1 hv1 hm hd M hM
  beta_reduce
  rw [← Finset.sum_add_distrib]
  refine Eq.symm ?_
  calc ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, 2 * (d : K)
        * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j))
              * (Gz v (d : ℤ) * xCoeff v (M - a))
          + (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j))
              * (Gz u (d : ℤ) * xCoeff u (M - a)))
      = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors,
          ((2 * (d : K))
              * (∑ k ∈ Finset.Ico 1 d, ((d : K) - (k : K)) * Gz u (k : ℤ))
              * (∑ p ∈ (M - a).divisors ×ˢ Finset.range 3,
                  (p.1 : K) * fgCoeff p.2 * Gz v (fgIdx (p.1 : ℤ) (d : ℤ) p.2))
            + (2 * (d : K))
              * (∑ p ∈ (M - a).divisors ×ˢ Finset.range 3,
                  (p.1 : K) * fgCoeff p.2 * Gz u (fgIdx (p.1 : ℤ) (d : ℤ) p.2))
              * (∑ k ∈ Finset.Ico 1 d, ((d : K) - (k : K)) * Gz v (k : ℤ))) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Gz_one_mul_telescope_eq_sum u hu d, Gz_one_mul_telescope_eq_sum v hv d,
          Gz_mul_xCoeff_eq_row v hv d (M - a), Gz_mul_xCoeff_eq_row u hu d (M - a)]
        ring
    _ = ∑ x ∈ (Finset.Ico 1 M).sigma (fun a => a.divisors),
          ((2 * (x.2 : K))
              * (∑ k ∈ Finset.Ico 1 x.2, ((x.2 : K) - (k : K)) * Gz u (k : ℤ))
              * (∑ p ∈ (M - x.1).divisors ×ˢ Finset.range 3,
                  (p.1 : K) * fgCoeff p.2 * Gz v (fgIdx (p.1 : ℤ) (x.2 : ℤ) p.2))
            + (2 * (x.2 : K))
              * (∑ p ∈ (M - x.1).divisors ×ˢ Finset.range 3,
                  (p.1 : K) * fgCoeff p.2 * Gz u (fgIdx (p.1 : ℤ) (x.2 : ℤ) p.2))
              * (∑ k ∈ Finset.Ico 1 x.2, ((x.2 : K) - (k : K)) * Gz v (k : ℤ))) :=
        Finset.sum_sigma' _ _ _

theorem hasCanonicalTable_svComplex [CharZero K] :
    HasCanonicalTable K fun u v M => svComplex u v M := by
  refine ((((hasCanonicalTable_svBlock1.sub hasCanonicalTable_svBlock2).add
      hasCanonicalTable_svBlock3).add hasCanonicalTable_svBlock4).sub
      hasCanonicalTable_svBlock5).congr ?_
  intro u v hu hv hu1 hv1 hm hd M hM
  beta_reduce
  exact (svComplex_eq_rowBlocks hu hu1 hv hv1 hm hd hM).symm

end SvComplex
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

section Final

variable [CharZero K] [DecidableEq K]
variable {q τ : K}

theorem diffHyp_of_regional_S1 (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v')) :
    DiffHyp q :=
  diffHyp_of_regional_S1_of_blocks hq0 hq hτ hregS1
    hasCanonicalTable_crossInteriorBlock hasCanonicalTable_svComplex

theorem diffHyp_of_regional_S1_of_isAlgClosed [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v')) :
    DiffHyp q := by
  obtain ⟨τ, hτ⟩ := exists_sqrt_of_isAlgClosed (K := K) q
  exact diffHyp_of_regional_S1 hq0 hq hτ hregS1

end Final
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

end TateCurve
p2m_reactivate "P2MW.S_TateCurve_diffHyp_unconditional.TateCurve"

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    TateCurve.DiffHyp q :=
  TateCurve.diffHyp_of_regional_S1_of_isAlgClosed hq0 hq (TateCurve.symAdd_sum_regional hq0 hq)

end S_TateCurve_diffHyp_unconditional
end P2MW
export P2MW.S_TateCurve_diffHyp_unconditional (solution)
