-- Prove2me | solution 1 for TateCurve.symAdd_sum_regional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3aae1b8e-203b-578b-ad72-c176623e1fc0

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab
import Theorems.Thm_TateCurve_ks17_A_exports
import Theorems.Thm_TateCurve_ks17_B_exports
import Theorems.Thm_TateCurve_ks17_C1_exports
import Theorems.Thm_TateCurve_ks17_C2_exports
import Theorems.Thm_TateCurve_ks17_C3_exports
import Theorems.Thm_TateCurve_ks17_D2_exports
import Theorems.Thm_TateCurve_ks17_D3_exports
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_symAdd_sum_regional
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"

open scoped NNReal
p2m_open "TateCurve~SymAddHyps P2MW.S_TateCurve_symAdd_sum_regional.TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset"

universe u_1 u_2

namespace TateCurve
p2m_export "TateCurve" "unitSpectator nnnorm_unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows symSumNum AddParams addDefectSum addDefectSum_eq_zero_iff addDefectSum_q_mul_left offLattice_of_norm_eq_one norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma cauchyMulInt Fz Gz Fz_natCast tent cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b a₄ a₆ curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C2_exports ks17_C3_exports ks17_D2_exports ks17_D3_exports"
p2m_open "TateCurve~SymAddHyps"

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

namespace AddParams p2m_export "TateCurve.AddParams" "swap v_ne_zero u_ne_zero offLattice_v offLattice_div offLattice_u offLattice_mul" end AddParams
p2m_open_scoped "TateCurve.AddParams" in
theorem AddParams.latticeRep : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} {u' v' : K} (hp : AddParams q u v)
    (hu' : LatticeRep q u u') (hv' : LatticeRep q v v'),
      AddParams q u' v' :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end TateCurve

namespace TateCurve
p2m_export "TateCurve" "unitSpectator nnnorm_unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows symSumNum AddParams addDefectSum addDefectSum_eq_zero_iff addDefectSum_q_mul_left offLattice_of_norm_eq_one norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma cauchyMulInt Fz Gz Fz_natCast tent cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b a₄ a₆ curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C2_exports ks17_C3_exports ks17_D2_exports ks17_D3_exports"
p2m_open "TateCurve~SymAddHyps"

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
p2m_export "TateCurve" "unitSpectator nnnorm_unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows symSumNum AddParams addDefectSum addDefectSum_eq_zero_iff addDefectSum_q_mul_left offLattice_of_norm_eq_one norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma cauchyMulInt Fz Gz Fz_natCast tent cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b a₄ a₆ curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C2_exports ks17_C3_exports ks17_D2_exports ks17_D3_exports"
p2m_open "TateCurve~SymAddHyps"

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
p2m_export "TateCurve" "unitSpectator nnnorm_unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows symSumNum AddParams addDefectSum addDefectSum_eq_zero_iff addDefectSum_q_mul_left offLattice_of_norm_eq_one norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma cauchyMulInt Fz Gz Fz_natCast tent cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b a₄ a₆ curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C2_exports ks17_C3_exports ks17_D2_exports ks17_D3_exports"
p2m_open "TateCurve~SymAddHyps"

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
p2m_export "TateCurve" "unitSpectator nnnorm_unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows symSumNum AddParams addDefectSum addDefectSum_eq_zero_iff addDefectSum_q_mul_left offLattice_of_norm_eq_one norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma cauchyMulInt Fz Gz Fz_natCast tent cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b a₄ a₆ curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C2_exports ks17_C3_exports ks17_D2_exports ks17_D3_exports"
p2m_open "TateCurve~SymAddHyps"

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
p2m_export "TateCurve" "unitSpectator nnnorm_unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows symSumNum AddParams addDefectSum addDefectSum_eq_zero_iff addDefectSum_q_mul_left offLattice_of_norm_eq_one norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma cauchyMulInt Fz Gz Fz_natCast tent cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b a₄ a₆ curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C2_exports ks17_C3_exports ks17_D2_exports ks17_D3_exports"
p2m_open "TateCurve~SymAddHyps"

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

namespace TateCurve
p2m_export "TateCurve" "unitSpectator nnnorm_unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows symSumNum AddParams addDefectSum addDefectSum_eq_zero_iff addDefectSum_q_mul_left offLattice_of_norm_eq_one norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma cauchyMulInt Fz Gz Fz_natCast tent cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b a₄ a₆ curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C2_exports ks17_C3_exports ks17_D2_exports ks17_D3_exports"
p2m_open "TateCurve~SymAddHyps"

theorem groupC_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      ∑ d ∈ M.divisors, (d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ))) + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ))) - 2 * ((d : K) ^ 2 * (d : K) ^ 2 + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ)) + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) = ((∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.1 = j), (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2) * Fz v (j : ℤ)) + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d, 2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = k ∧ q.1.1 = j), (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = k), 2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))) * Fz u (k : ℤ))) + ((∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.1 = k), (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2) * Fz u (k : ℤ)) + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d, 2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.1.1 = k ∧ q.2 = j), (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j), 2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))) * Fz v (j : ℤ))) - 2 * ((∑ d ∈ M.divisors, (d : K) * ((d : K) ^ 2 * (d : K) ^ 2)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.2 = k), (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K)) * Fz u (k : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.2 = j), (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K)) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.1).filter (fun q => q.2 = k ∧ q.1.2 = j), (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.1 - q.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ))) :=
  TateCurve.ks17_D3_exports.{u_1}.1

theorem groupD_tent_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ e ∈ (M - a).divisors, (d : K) * (e : K) * (Fz v (d : ℤ) * ((e : K) ^ 2 * Fz u (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ))) + 2 * ((e : K) ^ 2 * Fz u (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ))) + 2 * Fz v (d : ℤ) * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz u (l : ℤ))) = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k ∧ q.1.2 = j), (q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j), (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j), (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => r.1.1.2 = k ∧ r.1.1.2 = j), 2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k), 2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2)) * Fz u (k : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k), 2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))) * Fz u (k : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k), 2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))) * Fz u (k : ℤ)) - (∑ k ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => r.1.1.2 = k), 4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))) * Fz u (k : ℤ)) - (∑ k ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter (fun r => r.2 = k), 4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))) * Fz u (k : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j), 2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2)) * Fz v (j : ℤ)) :=
  TateCurve.ks17_D3_exports.{u_1}.2.1

theorem groupD_xCoeff_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (v : K) (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ d' ∈ (M - a).divisors, (d : K) * (d' : K) * ((Fz v ((d : ℤ) + (d' : ℤ)) + Fz v ((d : ℤ) - (d' : ℤ)) - 2 * Fz v (d : ℤ)) * tent u d) = ((∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).filter (fun q => ((q.1.2 : ℤ) + (q.2 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2) * Fz v (j : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).filter (fun q => ((q.1.2 : ℤ) - (q.2 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2) * Fz v (j : ℤ)) - (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j), 2 * ((q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)) * Fz v (j : ℤ))) + ((∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) + (r.1.2 : ℤ)).natAbs = j), (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) - (r.1.2 : ℤ)).natAbs = j), (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter (fun r => r.2 = k ∧ r.1.1.2 = j), 2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))) * Fz u (k : ℤ) * Fz v (j : ℤ))) :=
  TateCurve.ks17_D3_exports.{u_1}.2.2.1

theorem groupD_diffsq_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ x ∈ Sols (M - a), (d : K) * (x.1 : K) * (x.2.2.1 : K) * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ)) * ((Fz u (x.1 : ℤ) - Fz v (x.1 : ℤ)) * (Fz u (x.2.2.1 : ℤ) - Fz v (x.2.2.1 : ℤ))) = (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K) * ((Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))) + Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))) * Fz v (q.1.2 : ℤ) + Fz u (q.1.2 : ℤ) * (Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))) + Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))) + 4 * (Fz u (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ)) + 4 * (Fz u (q.2.2.2.1 : ℤ) * Fz v (q.2.1 : ℤ)) - (Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ))) * (Fz v ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ))) - (Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ))) * (Fz v ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.1 : ℤ))))) + 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K) * (Fz u (q.1.2 : ℤ) * Fz u (q.2.1 : ℤ) * Fz u (q.2.2.2.1 : ℤ))) + 2 * (∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K) * (Fz v (q.1.2 : ℤ) * Fz v (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ))) :=
  TateCurve.ks17_D3_exports.{u_1}.2.2.2.1

theorem groupD_diffsq_mixed_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K) * ((Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))) + Fz u ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz u ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))) * Fz v (q.1.2 : ℤ) + Fz u (q.1.2 : ℤ) * (Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))) + Fz v ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))) + Fz v ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)))) + 4 * (Fz u (q.2.1 : ℤ) * Fz v (q.2.2.2.1 : ℤ)) + 4 * (Fz u (q.2.2.2.1 : ℤ) * Fz v (q.2.1 : ℤ)) - (Fz u ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.1 : ℤ))) * (Fz v ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ))) - (Fz u ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)) + Fz u ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ))) * (Fz v ((q.1.2 : ℤ) + (q.2.1 : ℤ)) + Fz v ((q.1.2 : ℤ) - (q.2.1 : ℤ)))) = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k ∧ q.1.2 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k ∧ q.1.2 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k ∧ q.1.2 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k ∧ q.1.2 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + 4 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + 4 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.2.2.1 = k ∧ q.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) :=
  TateCurve.ks17_D3_exports.{u_1}.2.2.2.2.1

theorem groupD_diffsq_pure_eq_sum_lines : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (M : ℕ),
      ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K) * (Fz u (q.1.2 : ℤ) * Fz u (q.2.1 : ℤ) * Fz u (q.2.2.2.1 : ℤ)) = (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) + 4 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.1 + q.2.2.2.1 = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) + 4 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) + 4 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.2.2.1 = k), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ)) :=
  TateCurve.ks17_D3_exports.{u_1}.2.2.2.2.2

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "unitSpectator nnnorm_unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows symSumNum AddParams addDefectSum addDefectSum_eq_zero_iff addDefectSum_q_mul_left offLattice_of_norm_eq_one norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma cauchyMulInt Fz Gz Fz_natCast tent cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b a₄ a₆ curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C2_exports ks17_C3_exports ks17_D2_exports ks17_D3_exports"
p2m_open "TateCurve~SymAddHyps"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section IndexSets

def E1Idx (M : ℕ) : Finset (Σ _ : ℕ × ℕ × ℕ × ℕ, ℕ) :=
  (Sols M).sigma fun x => Finset.Ico 1 x.1

def E2Idx (M : ℕ) : Finset (Σ _ : ℕ × ℕ × ℕ × ℕ, ℕ) :=
  (Sols M).sigma fun x => Finset.Ico 1 x.2.2.1

def TIdx (M : ℕ) : Finset (Σ _ : (Σ _ : ℕ, ℕ), ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)

theorem E1Idx_eq (M : ℕ) : E1Idx M = (Sols M).sigma fun x => Finset.Ico 1 x.1 := rfl
theorem E2Idx_eq (M : ℕ) : E2Idx M = (Sols M).sigma fun x => Finset.Ico 1 x.2.2.1 := rfl
theorem TIdx_eq (M : ℕ) :
    TIdx M = ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1) := rfl

end IndexSets

section Totals

def intRowCoeff (M k j : ℕ) : ℤ :=
  (-4) * (∑ p ∈ (E1Idx M).filter (fun p => p.2 = k ∧ p.1.2.2.1 = j),
      (p.1.1 : ℤ) * ((p.1.1 - p.2 : ℕ) : ℤ) * (p.1.2.2.1 : ℤ))
    + (-4) * (∑ p ∈ (E2Idx M).filter (fun p => p.1.1 = k ∧ p.2 = j),
        (p.1.2.2.1 : ℤ) * ((p.1.2.2.1 - p.2 : ℕ) : ℤ) * (p.1.1 : ℤ))
    + (-2) * (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + 8 * (∑ q ∈ (TIdx M).filter (fun q => q.1.2 = k ∧ q.2.2.2.1 = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + 4 * (∑ q ∈ (TIdx M).filter (fun q => q.2.1 = k ∧ q.2.2.2.1 = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (TIdx M).filter
        (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (TIdx M).filter
        (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + 4 * (∑ q ∈ (TIdx M).filter (fun q => q.1.2 = k ∧ q.2.1 = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-1) * (∑ x ∈ (Sols M).filter (fun x => x.1 = k ∧ x.2.2.1 = j),
        (x.1 : ℤ) * (x.2.2.1 : ℤ))

def intURowCoeff (M k : ℕ) : ℤ :=
  (-4) * (∑ x ∈ (Sols M).filter (fun x => x.1 = k), (x.2.2.1 : ℤ) ^ 3 * (x.1 : ℤ))
    + (-2) * (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = k),
        -((5 * x.1 ^ 3 : ℕ) : ℤ) * (x.2.2.1 : ℤ))

def intVRowCoeff (M j : ℕ) : ℤ :=
  (-4) * (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = j), (x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ))
    + (-2) * (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = j),
        -((5 * x.1 ^ 3 : ℕ) : ℤ) * (x.2.2.1 : ℤ))

theorem intVRowCoeff_eq (M j : ℕ) :
    intVRowCoeff M j
      = 6 * ∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = j), (x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ) := by
  unfold intVRowCoeff
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by push_cast; ring

end Totals

section Cast

theorem intRowCoeff_cast (M k j : ℕ) :
    ((intRowCoeff M k j : ℤ) : K)
      = (-4 : K) * (∑ p ∈ ((Sols M).sigma fun x => Finset.Ico 1 x.1).filter
            (fun p => p.2 = k ∧ p.1.2.2.1 = j),
          (p.1.1 : K) * ((p.1.1 - p.2 : ℕ) : K) * (p.1.2.2.1 : K))
        + (-4 : K) * (∑ p ∈ ((Sols M).sigma fun x => Finset.Ico 1 x.2.2.1).filter
            (fun p => p.1.1 = k ∧ p.2 = j),
          (p.1.2.2.1 : K) * ((p.1.2.2.1 - p.2 : ℕ) : K) * (p.1.1 : K))
        + (-2 : K) * (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (8 : K) * (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.2.2.1 = j),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (4 : K) * (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k ∧ q.2.2.2.1 = j),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (4 : K) * (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.1 = j),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-1 : K) * (∑ x ∈ (Sols M).filter (fun x => x.1 = k ∧ x.2.2.1 = j),
          (x.1 : K) * (x.2.2.1 : K)) := by
  unfold intRowCoeff
  rw [E1Idx_eq, E2Idx_eq, TIdx_eq]
  push_cast
  ring

theorem intURowCoeff_cast (M k : ℕ) :
    ((intURowCoeff M k : ℤ) : K)
      = (-4 : K) * (∑ x ∈ (Sols M).filter (fun x => x.1 = k),
          (x.2.2.1 : K) ^ 3 * (x.1 : K))
        + (-2 : K) * (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = k),
          -((5 * x.1 ^ 3 : ℕ) : K) * (x.2.2.1 : K)) := by
  unfold intURowCoeff
  push_cast
  ring

theorem intVRowCoeff_cast (M j : ℕ) :
    ((intVRowCoeff M j : ℤ) : K)
      = (-4 : K) * (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = j),
          (x.1 : K) ^ 3 * (x.2.2.1 : K))
        + (-2 : K) * (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = j),
          -((5 * x.1 ^ 3 : ℕ) : K) * (x.2.2.1 : K)) := by
  unfold intVRowCoeff
  push_cast
  ring

end Cast

section SubAssembly

set_option maxHeartbeats 6400000 in

theorem interior_eq_sum_lines [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (M : ℕ) :
    (-4 : K) * (∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1)
        + (-4 : K) * (∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1))
        + (-2 : K) * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M
        + (-2 : K) * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M
        + (-1 : K) * cauchyMulInt (xCoeffFull u) (xCoeffFull v) M
        + (-2 : K) * cauchyMulInt a₄Coeff (xCoeffFull u) M
        + (-2 : K) * cauchyMulInt a₄Coeff (xCoeffFull v) M
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            ((intRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ((intURowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + (∑ j ∈ Finset.Icc 1 M, ((intVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ)) := by

  have hE1 := groupE1_eq_sum_lines hu0 hu1 v M
  have hE2 := groupE2_eq_sum_lines u hv0 hv1 M
  have hF := groupF_eq_sum_lines hu0 v M
  have hG := groupG_eq_sum_lines u hv0 M
  have hH := groupH_eq_sum_lines u v M
  have hI := groupI_eq_sum_lines u M
  have hJ := groupI_eq_sum_lines v M

  have hmix : (-4 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ p ∈ ((Sols M).sigma fun x => Finset.Ico 1 x.1).filter
              (fun p => p.2 = k ∧ p.1.2.2.1 = j),
            (p.1.1 : K) * ((p.1.1 - p.2 : ℕ) : K) * (p.1.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-4 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ p ∈ ((Sols M).sigma fun x => Finset.Ico 1 x.2.2.1).filter
              (fun p => p.1.1 = k ∧ p.2 = j),
            (p.1.2.2.1 : K) * ((p.1.2.2.1 - p.2 : ℕ) : K) * (p.1.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-2 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-2 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (8 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.2.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (4 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k ∧ q.2.2.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-2 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-2 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (4 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ x ∈ (Sols M).filter (fun x => x.1 = k ∧ x.2.2.1 = j),
            (x.1 : K) * (x.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((intRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intRowCoeff_cast]
    ring

  have hubin : (-4 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ x ∈ (Sols M).filter (fun x => x.1 = k), (x.2.2.1 : K) ^ 3 * (x.1 : K))
            * Fz u (k : ℤ))
        + (-2 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = k),
            -((5 * x.1 ^ 3 : ℕ) : K) * (x.2.2.1 : K)) * Fz u (k : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ((intURowCoeff M k : ℤ) : K) * Fz u (k : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intURowCoeff_cast]
    ring

  have hvbin : (-4 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = j), (x.1 : K) ^ 3 * (x.2.2.1 : K))
            * Fz v (j : ℤ))
        + (-2 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = j),
            -((5 * x.1 ^ 3 : ℕ) : K) * (x.2.2.1 : K)) * Fz v (j : ℤ))
      = ∑ j ∈ Finset.Icc 1 M, ((intVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intVRowCoeff_cast]
    ring
  linear_combination (-4 : K) * hE1 + (-4 : K) * hE2 + (-2 : K) * hF + (-2 : K) * hG
    + (-1 : K) * hH + (-2 : K) * hI + (-2 : K) * hJ + hmix + hubin + hvbin

end SubAssembly

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "unitSpectator nnnorm_unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows symSumNum AddParams addDefectSum addDefectSum_eq_zero_iff addDefectSum_q_mul_left offLattice_of_norm_eq_one norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma cauchyMulInt Fz Gz Fz_natCast tent cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b a₄ a₆ curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C2_exports ks17_C3_exports ks17_D2_exports ks17_D3_exports"
p2m_open "TateCurve~SymAddHyps"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section IndexSets

def AIdx (M : ℕ) : Finset (Σ _ : Σ _ : ℕ × ℕ × ℕ × ℕ, ℕ, ℕ) :=
  ((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1

def BIccIdxU (M : ℕ) : Finset (Σ _ : Σ _ : ℕ, ℕ, ℕ) :=
  (M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 (p.1 + 1 - p.2)

def BIccIdxV (M : ℕ) : Finset (Σ _ : Σ _ : ℕ, ℕ, ℕ) :=
  (M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 p.2

def BIccIdxM (M : ℕ) : Finset (Σ _ : Σ _ : Σ _ : ℕ, ℕ, ℕ, ℕ) :=
  ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 p.2).sigma
    fun r => Finset.Ico 1 (r.1.1 + 1 - r.1.2)

def BRngIdxU (M : ℕ) : Finset (Σ _ : Σ _ : ℕ, ℕ, ℕ) :=
  (M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 (p.1 - 1 - p.2)

def BRngIdxV (M : ℕ) : Finset (Σ _ : Σ _ : ℕ, ℕ, ℕ) :=
  (M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 p.2

def BRngIdxM (M : ℕ) : Finset (Σ _ : Σ _ : Σ _ : ℕ, ℕ, ℕ, ℕ) :=
  ((M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 p.2).sigma
    fun r => Finset.Ico 1 (r.1.1 - 1 - r.1.2)

def CIdx2 (M : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  M.divisors.sigma fun d => Finset.Ico 1 d

def CIdx3 (M : ℕ) : Finset (Σ _ : Σ _ : ℕ, ℕ, ℕ) :=
  (M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2

def CIdxD (M : ℕ) : Finset (Σ _ : Σ _ : ℕ, ℕ, ℕ) :=
  (M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.1

theorem AIdx_eq (M : ℕ) :
    AIdx M = ((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1 :=
  rfl
theorem BIccIdxU_eq (M : ℕ) :
    BIccIdxU M
      = (M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 (p.1 + 1 - p.2) :=
  rfl
theorem BIccIdxV_eq (M : ℕ) :
    BIccIdxV M = (M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 p.2 :=
  rfl
theorem BIccIdxM_eq (M : ℕ) :
    BIccIdxM M
      = ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 p.2).sigma
          fun r => Finset.Ico 1 (r.1.1 + 1 - r.1.2) :=
  rfl
theorem BRngIdxU_eq (M : ℕ) :
    BRngIdxU M
      = (M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 (p.1 - 1 - p.2) :=
  rfl
theorem BRngIdxV_eq (M : ℕ) :
    BRngIdxV M = (M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 p.2 :=
  rfl
theorem BRngIdxM_eq (M : ℕ) :
    BRngIdxM M
      = ((M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 p.2).sigma
          fun r => Finset.Ico 1 (r.1.1 - 1 - r.1.2) :=
  rfl
theorem CIdx2_eq (M : ℕ) : CIdx2 M = M.divisors.sigma fun d => Finset.Ico 1 d := rfl
theorem CIdx3_eq (M : ℕ) :
    CIdx3 M = (M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.2 := rfl
theorem CIdxD_eq (M : ℕ) :
    CIdxD M = (M.divisors.sigma fun d => Finset.Ico 1 d).sigma fun p => Finset.Ico 1 p.1 := rfl

end IndexSets

section Totals

def bdryRowCoeff (M k j : ℕ) : ℤ :=
  (∑ q ∈ (AIdx M).filter
      (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k ∧
        ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j),
      (q.1.1.1 : ℤ) * (q.1.1.2.2.1 : ℤ))
    + (-1) * (∑ q ∈ (AIdx M).filter
        (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k ∧
          ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j),
        (q.1.1.1 : ℤ) * (q.1.1.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (BIccIdxM M).filter (fun q => q.2 = k ∧ q.1.2 = j),
        (q.1.1.1 : ℤ) * ((q.1.1.2 - q.1.2 : ℕ) : ℤ) * ((q.1.1.1 + 1 - q.1.1.2 - q.2 : ℕ) : ℤ))
    + 2 * (∑ q ∈ (BRngIdxM M).filter (fun q => q.2 = k ∧ q.1.2 = j),
        (q.1.1.1 : ℤ) * ((q.1.1.2 - q.1.2 : ℕ) : ℤ) * ((q.1.1.1 - 1 - q.1.1.2 - q.2 : ℕ) : ℤ))
    + (∑ q ∈ (CIdx3 M).filter (fun q => q.2 = k ∧ q.1.1 = j),
        (q.1.1 : ℤ) * ((q.1.1 - q.1.2 : ℕ) : ℤ) * ((q.1.2 - q.2 : ℕ) : ℤ))
    + (∑ q ∈ (CIdx3 M).filter (fun q => q.1.1 = k ∧ q.2 = j),
        (q.1.1 : ℤ) * ((q.1.1 - q.1.2 : ℕ) : ℤ) * ((q.1.2 - q.2 : ℕ) : ℤ))
    + (-2) * (∑ q ∈ (CIdxD M).filter (fun q => q.2 = k ∧ q.1.2 = j),
        (q.1.1 : ℤ) * ((q.1.1 - q.1.2 : ℕ) : ℤ) * ((q.1.1 - q.2 : ℕ) : ℤ))

def bdryURowCoeff (M k : ℕ) : ℤ :=
  2 * (∑ q ∈ (AIdx M).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k),
      (q.1.1.1 : ℤ) * (q.1.1.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (AIdx M).filter
        (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k),
        (q.1.1.1 : ℤ) * (q.1.1.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (BIccIdxU M).filter (fun q => q.2 = k),
        (q.1.1 : ℤ) * (q.1.2 : ℤ) ^ 2 * ((q.1.1 + 1 - q.1.2 - q.2 : ℕ) : ℤ))
    + 2 * (∑ q ∈ (BRngIdxU M).filter (fun q => q.2 = k),
        (q.1.1 : ℤ) * (q.1.2 : ℤ) ^ 2 * ((q.1.1 - 1 - q.1.2 - q.2 : ℕ) : ℤ))
    + (∑ q ∈ (CIdx3 M).filter (fun q => q.2 = k),
        2 * ((q.1.1 : ℤ) * ((q.1.1 - q.1.2 : ℕ) : ℤ) * ((q.1.2 - q.2 : ℕ) : ℤ)))
    + (∑ q ∈ (CIdx2 M).filter (fun q => q.1 = k),
        (q.1 : ℤ) * ((q.1 - q.2 : ℕ) : ℤ) * (q.2 : ℤ) ^ 2)
    + (-2) * (∑ q ∈ (CIdx2 M).filter (fun q => q.2 = k),
        (q.1 : ℤ) * (q.1 : ℤ) ^ 2 * ((q.1 - q.2 : ℕ) : ℤ))

def bdryVRowCoeff (M j : ℕ) : ℤ :=
  2 * (∑ q ∈ (AIdx M).filter
      (fun q => ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j),
      (q.1.1.1 : ℤ) * (q.1.1.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (AIdx M).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j),
        (q.1.1.1 : ℤ) * (q.1.1.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (BIccIdxV M).filter (fun q => q.2 = j),
        (q.1.1 : ℤ) * ((q.1.1 + 1 - q.1.2 : ℕ) : ℤ) ^ 2 * ((q.1.2 - q.2 : ℕ) : ℤ))
    + 2 * (∑ q ∈ (BRngIdxV M).filter (fun q => q.2 = j),
        (q.1.1 : ℤ) * ((q.1.1 - 1 - q.1.2 : ℕ) : ℤ) ^ 2 * ((q.1.2 - q.2 : ℕ) : ℤ))
    + (∑ q ∈ (CIdx2 M).filter (fun q => q.1 = j),
        (q.1 : ℤ) * ((q.1 - q.2 : ℕ) : ℤ) * (q.2 : ℤ) ^ 2)
    + (∑ q ∈ (CIdx3 M).filter (fun q => q.2 = j),
        2 * ((q.1.1 : ℤ) * ((q.1.1 - q.1.2 : ℕ) : ℤ) * ((q.1.2 - q.2 : ℕ) : ℤ)))
    + (-2) * (∑ q ∈ (CIdx2 M).filter (fun q => q.2 = j),
        (q.1 : ℤ) * (q.1 : ℤ) ^ 2 * ((q.1 - q.2 : ℕ) : ℤ))

end Totals

section Cast

theorem bdryRowCoeff_cast (M k j : ℕ) :
    ((bdryRowCoeff M k j : ℤ) : K)
      = (1 : K) * (∑ q ∈ ((((Sols M).sigma fun x => Finset.range x.1).sigma
            fun p => Finset.range p.1.2.2.1).filter
              (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k ∧
                ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j)),
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
        + (-1 : K) * (∑ q ∈ ((((Sols M).sigma fun x => Finset.range x.1).sigma
            fun p => Finset.range p.1.2.2.1).filter
              (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k ∧
                ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j)),
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ ((((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
            fun p => Finset.Ico 1 p.2).sigma
              fun r => Finset.Ico 1 (r.1.1 + 1 - r.1.2)).filter
                (fun q => q.2 = k ∧ q.1.2 = j)),
          (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K)
            * ((q.1.1.1 + 1 - q.1.1.2 - q.2 : ℕ) : K))
        + (2 : K) * (∑ q ∈ ((((M.divisors.sigma fun d => Finset.range d).sigma
            fun p => Finset.Ico 1 p.2).sigma
              fun r => Finset.Ico 1 (r.1.1 - 1 - r.1.2)).filter
                (fun q => q.2 = k ∧ q.1.2 = j)),
          (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K)
            * ((q.1.1.1 - 1 - q.1.1.2 - q.2 : ℕ) : K))
        + (1 : K) * (∑ q ∈ (((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
            fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = k ∧ q.1.1 = j)),
          (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))
        + (1 : K) * (∑ q ∈ (((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
            fun p => Finset.Ico 1 p.2).filter (fun q => q.1.1 = k ∧ q.2 = j)),
          (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))
        + (-2 : K) * (∑ q ∈ (((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
            fun p => Finset.Ico 1 p.1).filter (fun q => q.2 = k ∧ q.1.2 = j)),
          (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.1 - q.2 : ℕ) : K)) := by
  unfold bdryRowCoeff
  rw [AIdx_eq, BIccIdxM_eq, BRngIdxM_eq, CIdx3_eq, CIdxD_eq]
  push_cast
  ring

theorem bdryURowCoeff_cast (M k : ℕ) :
    ((bdryURowCoeff M k : ℤ) : K)
      = (2 : K) * (∑ q ∈ ((((Sols M).sigma fun x => Finset.range x.1).sigma
            fun p => Finset.range p.1.2.2.1).filter
              (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k)),
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ ((((Sols M).sigma fun x => Finset.range x.1).sigma
            fun p => Finset.range p.1.2.2.1).filter
              (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k)),
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ (((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
            fun p => Finset.Ico 1 (p.1 + 1 - p.2)).filter (fun q => q.2 = k)),
          (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 + 1 - q.1.2 - q.2 : ℕ) : K))
        + (2 : K) * (∑ q ∈ (((M.divisors.sigma fun d => Finset.range d).sigma
            fun p => Finset.Ico 1 (p.1 - 1 - p.2)).filter (fun q => q.2 = k)),
          (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 - 1 - q.1.2 - q.2 : ℕ) : K))
        + (1 : K) * (∑ q ∈ (((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
            fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = k)),
          2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)))
        + (1 : K) * (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).filter
            (fun q => q.1 = k)),
          (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2)
        + (-2 : K) * (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).filter
            (fun q => q.2 = k)),
          (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K)) := by
  unfold bdryURowCoeff
  rw [AIdx_eq, BIccIdxU_eq, BRngIdxU_eq, CIdx3_eq, CIdx2_eq]
  push_cast
  ring

theorem bdryVRowCoeff_cast (M j : ℕ) :
    ((bdryVRowCoeff M j : ℤ) : K)
      = (2 : K) * (∑ q ∈ ((((Sols M).sigma fun x => Finset.range x.1).sigma
            fun p => Finset.range p.1.2.2.1).filter
              (fun q => ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j)),
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ ((((Sols M).sigma fun x => Finset.range x.1).sigma
            fun p => Finset.range p.1.2.2.1).filter
              (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j)),
          (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ (((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
            fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j)),
          (q.1.1 : K) * ((q.1.1 + 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K))
        + (2 : K) * (∑ q ∈ (((M.divisors.sigma fun d => Finset.range d).sigma
            fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j)),
          (q.1.1 : K) * ((q.1.1 - 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K))
        + (1 : K) * (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).filter
            (fun q => q.1 = j)),
          (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2)
        + (1 : K) * (∑ q ∈ (((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
            fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j)),
          2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)))
        + (-2 : K) * (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).filter
            (fun q => q.2 = j)),
          (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K)) := by
  unfold bdryVRowCoeff
  rw [AIdx_eq, BIccIdxV_eq, BRngIdxV_eq, CIdx2_eq, CIdx3_eq]
  push_cast
  ring

end Cast

section ConstantBin

theorem boundaryConst_eq_zero [CharZero K] {M : ℕ} (hM : 0 < M) :
    (-2 : K) * (∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
          (d : K) * ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2))
      + (2 : K) * (∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
          (d : K) * ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2))
      + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
          2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2))
      + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
          2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2))
      + (-2 : K) * (∑ d ∈ M.divisors, (d : K) * ((d : K) ^ 2 * (d : K) ^ 2))
      - 4 * a₆Coeff M = 0 := by

  have hcB : (∑ d ∈ M.divisors, (d : K) *
        ((∑ j ∈ Finset.Icc 1 d, (j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2)
          - ∑ j ∈ Finset.range d, (j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2))
      = (∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d,
            (d : K) * ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2))
        - ∑ d ∈ M.divisors, ∑ j ∈ Finset.range d,
            (d : K) * ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum]

  have hcC : (∑ d ∈ M.divisors, (d : K) *
        (2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2
          + 2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2
          - 2 * ((d : K) ^ 2 * (d : K) ^ 2)))
      = (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
            2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2))
        + (∑ d ∈ M.divisors, ∑ k ∈ Finset.Ico 1 d,
            2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2))
        - 2 * ∑ d ∈ M.divisors, (d : K) * ((d : K) ^ 2 * (d : K) ^ 2) := by
    rw [Finset.mul_sum (s := M.divisors)
      (f := fun d => (d : K) * ((d : K) ^ 2 * (d : K) ^ 2)) (a := (2 : K)),
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hA : ∑ k ∈ Finset.Ico 1 d, 2 * ((d : K) * ((d - k : ℕ) : K) * (k : K) ^ 2)
        = (d : K) * (2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    linear_combination (-2 : K) * hA
  linear_combination constantBin_eq_zero (K := K) hM + 2 * hcB - hcC

end ConstantBin

section SubAssembly

set_option maxHeartbeats 25600000 in

theorem boundaryOuter_eq_sum_lines [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) {M : ℕ} (hM : 0 < M) :
    (∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) *
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
        - 4 * a₆Coeff M
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            ((bdryRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ((bdryURowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + (∑ j ∈ Finset.Icc 1 M, ((bdryVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ)) := by

  have hAf := groupA_cross_Fread hu0 hv0 M
  have hAc := groupA_eq_sum_lines u v M
  have hBf := groupB_tent_Fread hu0 hu1 hv0 hv1 M
  have hBc := groupB_eq_sum_lines u v M
  have hCf := groupC_square_Fread hu0 hu1 hv0 hv1 M
  have hCc := groupC_eq_sum_lines u v M

  have hzero := boundaryConst_eq_zero (K := K) (M := M) hM

  have hmix : (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
              fun p => Finset.range p.1.2.2.1).filter
                (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k ∧
                  ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j),
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
              fun p => Finset.range p.1.2.2.1).filter
                (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k ∧
                  ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j),
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-2 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
              fun p => Finset.Ico 1 p.2).sigma
                fun r => Finset.Ico 1 (r.1.1 + 1 - r.1.2)).filter
                  (fun q => q.2 = k ∧ q.1.2 = j),
            (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K)
              * ((q.1.1.1 + 1 - q.1.1.2 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (2 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((M.divisors.sigma fun d => Finset.range d).sigma
              fun p => Finset.Ico 1 p.2).sigma
                fun r => Finset.Ico 1 (r.1.1 - 1 - r.1.2)).filter
                  (fun q => q.2 = k ∧ q.1.2 = j),
            (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K)
              * ((q.1.1.1 - 1 - q.1.1.2 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
              fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = k ∧ q.1.1 = j),
            (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
              fun p => Finset.Ico 1 p.2).filter (fun q => q.1.1 = k ∧ q.2 = j),
            (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-2 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
              fun p => Finset.Ico 1 p.1).filter (fun q => q.2 = k ∧ q.1.2 = j),
            (q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.1 - q.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((bdryRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bdryRowCoeff_cast]
    ring

  have hubin : (2 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
              fun p => Finset.range p.1.2.2.1).filter
                (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k),
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
            * Fz u (k : ℤ))
        + (-2 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
              fun p => Finset.range p.1.2.2.1).filter
                (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k),
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
            * Fz u (k : ℤ))
        + (-2 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
              fun p => Finset.Ico 1 (p.1 + 1 - p.2)).filter (fun q => q.2 = k),
            (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 + 1 - q.1.2 - q.2 : ℕ) : K))
            * Fz u (k : ℤ))
        + (2 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma
              fun p => Finset.Ico 1 (p.1 - 1 - p.2)).filter (fun q => q.2 = k),
            (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 - 1 - q.1.2 - q.2 : ℕ) : K))
            * Fz u (k : ℤ))
        + (1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
              fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = k),
            2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)))
            * Fz u (k : ℤ))
        + (1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.1 = k),
            (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2)
            * Fz u (k : ℤ))
        + (-2 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.2 = k),
            (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K))
            * Fz u (k : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ((bdryURowCoeff M k : ℤ) : K) * Fz u (k : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [bdryURowCoeff_cast]
    ring

  have hvbin : (2 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
              fun p => Finset.range p.1.2.2.1).filter
                (fun q => ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j),
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
            * Fz v (j : ℤ))
        + (-2 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma
              fun p => Finset.range p.1.2.2.1).filter
                (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j),
            (q.1.1.1 : K) * (q.1.1.2.2.1 : K))
            * Fz v (j : ℤ))
        + (-2 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma
              fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j),
            (q.1.1 : K) * ((q.1.1 + 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K))
            * Fz v (j : ℤ))
        + (2 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma
              fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j),
            (q.1.1 : K) * ((q.1.1 - 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K))
            * Fz v (j : ℤ))
        + (1 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.1 = j),
            (q.1 : K) * ((q.1 - q.2 : ℕ) : K) * (q.2 : K) ^ 2)
            * Fz v (j : ℤ))
        + (1 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ ((M.divisors.sigma fun d => Finset.Ico 1 d).sigma
              fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j),
            2 * ((q.1.1 : K) * ((q.1.1 - q.1.2 : ℕ) : K) * ((q.1.2 - q.2 : ℕ) : K)))
            * Fz v (j : ℤ))
        + (-2 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (M.divisors.sigma fun d => Finset.Ico 1 d).filter (fun q => q.2 = j),
            (q.1 : K) * (q.1 : K) ^ 2 * ((q.1 - q.2 : ℕ) : K))
            * Fz v (j : ℤ))
      = ∑ j ∈ Finset.Icc 1 M, ((bdryVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bdryVRowCoeff_cast]
    ring
  linear_combination hAf + hAc - 2 * hBf - 2 * hBc + hCf + hCc + hmix + hubin + hvbin + hzero

end SubAssembly

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TateCurve
p2m_export "TateCurve" "unitSpectator nnnorm_unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows symSumNum AddParams addDefectSum addDefectSum_eq_zero_iff addDefectSum_q_mul_left offLattice_of_norm_eq_one norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma cauchyMulInt Fz Gz Fz_natCast tent cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b a₄ a₆ curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C2_exports ks17_C3_exports ks17_D2_exports ks17_D3_exports"
p2m_open "TateCurve~SymAddHyps"

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section IndexSets

def DIdx3 (M : ℕ) : Finset (Σ _ : Σ _ : ℕ, ℕ, ℕ) :=
  ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors

def DTIdx (M : ℕ) : Finset (Σ _ : Σ _ : Σ _ : ℕ, ℕ, ℕ, ℕ) :=
  (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma
    fun q => Finset.Ico 1 q.2

def DXIdx (M : ℕ) : Finset (Σ _ : Σ _ : Σ _ : ℕ, ℕ, ℕ, ℕ) :=
  (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors).sigma
    fun q => Finset.Ico 1 q.1.2

theorem DIdx3_eq (M : ℕ) :
    DIdx3 M = ((Finset.Ico 1 M).sigma fun a => a.divisors).sigma fun p => (M - p.1).divisors :=
  rfl
theorem DTIdx_eq (M : ℕ) :
    DTIdx M = (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
      fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2 := rfl
theorem DXIdx_eq (M : ℕ) :
    DXIdx M = (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
      fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2 := rfl

end IndexSets

section TentBlock

def dTentRowCoeff (M k j : ℕ) : ℤ :=
  (∑ q ∈ (DIdx3 M).filter (fun q => q.1.2 = k ∧ q.1.2 = j),
      (q.1.2 : ℤ) * (q.2 : ℤ) * (q.2 : ℤ) ^ 2)
    + (∑ r ∈ (DTIdx M).filter
        (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j),
        (r.1.1.2 : ℤ) * (r.1.2 : ℤ) * ((r.1.2 - r.2 : ℕ) : ℤ))
    + (∑ r ∈ (DTIdx M).filter
        (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j),
        (r.1.1.2 : ℤ) * (r.1.2 : ℤ) * ((r.1.2 - r.2 : ℕ) : ℤ))
    + (-1) * (∑ r ∈ (DTIdx M).filter (fun r => r.1.1.2 = k ∧ r.1.1.2 = j),
        2 * ((r.1.1.2 : ℤ) * (r.1.2 : ℤ) * ((r.1.2 - r.2 : ℕ) : ℤ)))

def dTentURowCoeff (M k : ℕ) : ℤ :=
  (∑ q ∈ (DIdx3 M).filter (fun q => q.1.2 = k),
      2 * ((q.1.2 : ℤ) * (q.2 : ℤ) * (q.2 : ℤ) ^ 2))
    + (∑ r ∈ (DTIdx M).filter (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k),
        2 * ((r.1.1.2 : ℤ) * (r.1.2 : ℤ) * ((r.1.2 - r.2 : ℕ) : ℤ)))
    + (∑ r ∈ (DTIdx M).filter (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k),
        2 * ((r.1.1.2 : ℤ) * (r.1.2 : ℤ) * ((r.1.2 - r.2 : ℕ) : ℤ)))
    + (-1) * (∑ r ∈ (DTIdx M).filter (fun r => r.1.1.2 = k),
        4 * ((r.1.1.2 : ℤ) * (r.1.2 : ℤ) * ((r.1.2 - r.2 : ℕ) : ℤ)))
    + (-1) * (∑ r ∈ (DTIdx M).filter (fun r => r.2 = k),
        4 * ((r.1.1.2 : ℤ) * (r.1.2 : ℤ) * ((r.1.2 - r.2 : ℕ) : ℤ)))

def dTentVRowCoeff (M j : ℕ) : ℤ :=
  ∑ q ∈ (DIdx3 M).filter (fun q => q.1.2 = j),
    2 * ((q.1.2 : ℤ) * (q.2 : ℤ) * (q.2 : ℤ) ^ 2)

theorem dTentRowCoeff_cast (M k j : ℕ) :
    ((dTentRowCoeff M k j : ℤ) : K)
      = (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k ∧ q.1.2 = j)),
          (q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2)
        + (1 : K) * (∑ r ∈ (((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
              (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j)),
          (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
        + (1 : K) * (∑ r ∈ (((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
              (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j)),
          (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
        + (-1 : K) * (∑ r ∈ (((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
              (fun r => r.1.1.2 = k ∧ r.1.1.2 = j)),
          2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))) := by
  unfold dTentRowCoeff
  rw [DIdx3_eq, DTIdx_eq]
  push_cast
  ring

theorem dTentURowCoeff_cast (M k : ℕ) :
    ((dTentURowCoeff M k : ℤ) : K)
      = (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k)),
          2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2))
        + (1 : K) * (∑ r ∈ (((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
              (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k)),
          2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
        + (1 : K) * (∑ r ∈ (((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
              (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k)),
          2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
        + (-1 : K) * (∑ r ∈ (((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
              (fun r => r.1.1.2 = k)),
          4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
        + (-1 : K) * (∑ r ∈ (((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
              (fun r => r.2 = k)),
          4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))) := by
  unfold dTentURowCoeff
  rw [DIdx3_eq, DTIdx_eq]
  push_cast
  ring

theorem dTentVRowCoeff_cast (M j : ℕ) :
    ((dTentVRowCoeff M j : ℤ) : K)
      = (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j)),
          2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2)) := by
  unfold dTentVRowCoeff
  rw [DIdx3_eq]
  push_cast
  ring

set_option maxHeartbeats 12800000 in

theorem dTent_bins_merge (u v : K) (M : ℕ) :
    (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k ∧ q.1.2 = j),
            (q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2)
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j),
            (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j),
            (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => r.1.1.2 = k ∧ r.1.1.2 = j),
            2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + ((1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k),
            2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2))
            * Fz u (k : ℤ))
        + (1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k),
            2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ))
        + (1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k),
            2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ))
        + (-1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => r.1.1.2 = k),
            4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ))
        + (-1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => r.2 = k),
            4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ)))
      + (1 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j),
            2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2))
            * Fz v (j : ℤ))
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            ((dTentRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ((dTentURowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + (∑ j ∈ Finset.Icc 1 M, ((dTentVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ)) := by

  have hmix : (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k ∧ q.1.2 = j),
            (q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2)
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j),
            (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k ∧ r.1.1.2 = j),
            (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => r.1.1.2 = k ∧ r.1.1.2 = j),
            2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((dTentRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dTentRowCoeff_cast]
    ring

  have hubin : (1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter (fun q => q.1.2 = k),
            2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2))
            * Fz u (k : ℤ))
        + (1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => ((r.1.1.2 : ℤ) + (r.2 : ℤ)).natAbs = k),
            2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ))
        + (1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => ((r.1.1.2 : ℤ) - (r.2 : ℤ)).natAbs = k),
            2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ))
        + (-1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => r.1.1.2 = k),
            4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ))
        + (-1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.2).filter
                (fun r => r.2 = k),
            4 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ((dTentURowCoeff M k : ℤ) : K) * Fz u (k : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dTentURowCoeff_cast]
    ring

  have hvbin : (1 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j),
            2 * ((q.1.2 : K) * (q.2 : K) * (q.2 : K) ^ 2))
            * Fz v (j : ℤ))
      = ∑ j ∈ Finset.Icc 1 M, ((dTentVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dTentVRowCoeff_cast]
    ring
  linear_combination hmix + hubin + hvbin

set_option maxHeartbeats 12800000 in

theorem groupDTentU_eq_bins [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (M : ℕ) :
    ∑ a ∈ Finset.Ico 1 M,
        (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
          * (∑ e ∈ (M - a).divisors, (e : K) * tent u e)
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            ((dTentRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ((dTentURowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + (∑ j ∈ Finset.Icc 1 M, ((dTentVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ)) := by
  have h1 := groupD_cross_tent_Fread (u := u) (v := v) hu0 hu1 hv0 M
  have h2 := groupD_tent_eq_sum_lines (K := K) u v M
  have h3 := dTent_bins_merge (K := K) u v M
  linear_combination h1 + h2 + h3

set_option maxHeartbeats 12800000 in

theorem groupDTentV_eq_bins [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hv1 : v ≠ 1) (M : ℕ) :
    ∑ a ∈ Finset.Ico 1 M,
        (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
          * (∑ e ∈ (M - a).divisors, (e : K) * tent v e)
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            ((dTentRowCoeff M j k : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ((dTentVRowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + (∑ j ∈ Finset.Icc 1 M, ((dTentURowCoeff M j : ℤ) : K) * Fz v (j : ℤ)) := by
  have h1 := groupD_cross_tent_Fread' (u := u) (v := v) hu0 hv0 hv1 M
  have h2 := groupD_tent_eq_sum_lines (K := K) v u M
  have h3 := dTent_bins_merge (K := K) v u M

  have hswap : (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
        ((dTentRowCoeff M k j : ℤ) : K) * Fz v (k : ℤ) * Fz u (j : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((dTentRowCoeff M j k : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  linear_combination h1 + h2 + h3 + hswap

end TentBlock

section XColBlock

def dXColRowCoeff (M k j : ℕ) : ℤ :=
  (∑ r ∈ (DXIdx M).filter
      (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) + (r.1.2 : ℤ)).natAbs = j),
      (r.1.1.2 : ℤ) * (r.1.2 : ℤ) * ((r.1.1.2 - r.2 : ℕ) : ℤ))
    + (∑ r ∈ (DXIdx M).filter
        (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) - (r.1.2 : ℤ)).natAbs = j),
        (r.1.1.2 : ℤ) * (r.1.2 : ℤ) * ((r.1.1.2 - r.2 : ℕ) : ℤ))
    + (-1) * (∑ r ∈ (DXIdx M).filter (fun r => r.2 = k ∧ r.1.1.2 = j),
        2 * ((r.1.1.2 : ℤ) * (r.1.2 : ℤ) * ((r.1.1.2 - r.2 : ℕ) : ℤ)))

def dXColVRowCoeff (M j : ℕ) : ℤ :=
  (∑ q ∈ (DIdx3 M).filter (fun q => ((q.1.2 : ℤ) + (q.2 : ℤ)).natAbs = j),
      (q.1.2 : ℤ) * (q.2 : ℤ) * (q.1.2 : ℤ) ^ 2)
    + (∑ q ∈ (DIdx3 M).filter (fun q => ((q.1.2 : ℤ) - (q.2 : ℤ)).natAbs = j),
        (q.1.2 : ℤ) * (q.2 : ℤ) * (q.1.2 : ℤ) ^ 2)
    + (-1) * (∑ q ∈ (DIdx3 M).filter (fun q => q.1.2 = j),
        2 * ((q.1.2 : ℤ) * (q.2 : ℤ) * (q.1.2 : ℤ) ^ 2))

theorem dXColRowCoeff_cast (M k j : ℕ) :
    ((dXColRowCoeff M k j : ℤ) : K)
      = (1 : K) * (∑ r ∈ (((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
              (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) + (r.1.2 : ℤ)).natAbs = j)),
          (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
        + (1 : K) * (∑ r ∈ (((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
              (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) - (r.1.2 : ℤ)).natAbs = j)),
          (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
        + (-1 : K) * (∑ r ∈ (((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
              (fun r => r.2 = k ∧ r.1.1.2 = j)),
          2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))) := by
  unfold dXColRowCoeff
  rw [DXIdx_eq]
  push_cast
  ring

theorem dXColVRowCoeff_cast (M j : ℕ) :
    ((dXColVRowCoeff M j : ℤ) : K)
      = (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).filter
              (fun q => ((q.1.2 : ℤ) + (q.2 : ℤ)).natAbs = j)),
          (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)
        + (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).filter
              (fun q => ((q.1.2 : ℤ) - (q.2 : ℤ)).natAbs = j)),
          (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)
        + (-1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
            fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j)),
          2 * ((q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)) := by
  unfold dXColVRowCoeff
  rw [DIdx3_eq]
  push_cast
  ring

set_option maxHeartbeats 12800000 in

theorem dXCol_bins_merge (u v : K) (M : ℕ) :
    (1 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter
                (fun q => ((q.1.2 : ℤ) + (q.2 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)
            * Fz v (j : ℤ))
      + (1 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter
                (fun q => ((q.1.2 : ℤ) - (q.2 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)
            * Fz v (j : ℤ))
      + (-1 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j),
            2 * ((q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2))
            * Fz v (j : ℤ))
      + ((1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
                (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) + (r.1.2 : ℤ)).natAbs = j),
            (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
                (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) - (r.1.2 : ℤ)).natAbs = j),
            (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
                (fun r => r.2 = k ∧ r.1.1.2 = j),
            2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ) * Fz v (j : ℤ)))
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            ((dXColRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ j ∈ Finset.Icc 1 M, ((dXColVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ)) := by

  have hmix : (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
                (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) + (r.1.2 : ℤ)).natAbs = j),
            (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
                (fun r => r.2 = k ∧ ((r.1.1.2 : ℤ) - (r.1.2 : ℤ)).natAbs = j),
            (r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ r ∈ ((((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).sigma fun q => Finset.Ico 1 q.1.2).filter
                (fun r => r.2 = k ∧ r.1.1.2 = j),
            2 * ((r.1.1.2 : K) * (r.1.2 : K) * ((r.1.1.2 - r.2 : ℕ) : K)))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((dXColRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dXColRowCoeff_cast]
    ring

  have hvbin : (1 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter
                (fun q => ((q.1.2 : ℤ) + (q.2 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)
            * Fz v (j : ℤ))
        + (1 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter
                (fun q => ((q.1.2 : ℤ) - (q.2 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2)
            * Fz v (j : ℤ))
        + (-1 : K) * (∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun a => a.divisors).sigma
              fun p => (M - p.1).divisors).filter (fun q => q.1.2 = j),
            2 * ((q.1.2 : K) * (q.2 : K) * (q.1.2 : K) ^ 2))
            * Fz v (j : ℤ))
      = ∑ j ∈ Finset.Icc 1 M, ((dXColVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dXColVRowCoeff_cast]
    ring
  linear_combination hmix + hvbin

set_option maxHeartbeats 12800000 in

theorem groupDXColU_eq_bins [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (M : ℕ) :
    ∑ a ∈ Finset.Ico 1 M,
        (∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d) * xCoeff v (M - a)
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            ((dXColRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ j ∈ Finset.Icc 1 M, ((dXColVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ)) := by
  have h1 := groupD_psi_xCoeff_Fread (u := u) (v := v) hv0 M
  have h2 := groupD_xCoeff_eq_sum_lines (u := u) hu0 hu1 v M
  have h3 := dXCol_bins_merge (K := K) u v M
  linear_combination h1 + h2 + h3

set_option maxHeartbeats 12800000 in

theorem groupDXColV_eq_bins [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hv1 : v ≠ 1) (M : ℕ) :
    ∑ a ∈ Finset.Ico 1 M,
        (∑ d ∈ a.divisors, (d : K) * (Fz u (d : ℤ) + 2) * tent v d) * xCoeff u (M - a)
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            ((dXColRowCoeff M j k : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ((dXColVRowCoeff M k : ℤ) : K) * Fz u (k : ℤ)) := by
  have h1 := groupD_psi_xCoeff_Fread (u := v) (v := u) hu0 M
  have h2 := groupD_xCoeff_eq_sum_lines (u := v) hv0 hv1 u M
  have h3 := dXCol_bins_merge (K := K) v u M

  have hswap : (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
        ((dXColRowCoeff M k j : ℤ) : K) * Fz v (k : ℤ) * Fz u (j : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((dXColRowCoeff M j k : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  linear_combination h1 + h2 + h3 + hswap

end XColBlock

section DiffsqBlock

def dDiffRowCoeff (M k j : ℕ) : ℤ :=
  (∑ q ∈ (TIdx M).filter
      (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k ∧ q.1.2 = j),
      (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k ∧ q.1.2 = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k ∧ q.1.2 = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k ∧ q.1.2 = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (∑ q ∈ (TIdx M).filter
        (fun q => q.1.2 = k ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (∑ q ∈ (TIdx M).filter
        (fun q => q.1.2 = k ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (∑ q ∈ (TIdx M).filter
        (fun q => q.1.2 = k ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (∑ q ∈ (TIdx M).filter
        (fun q => q.1.2 = k ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + 4 * (∑ q ∈ (TIdx M).filter (fun q => q.2.1 = k ∧ q.2.2.2.1 = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + 4 * (∑ q ∈ (TIdx M).filter (fun q => q.2.2.2.1 = k ∧ q.2.1 = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-1) * (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k
          ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-1) * (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k
          ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-1) * (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k
          ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-1) * (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k
          ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-1) * (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k
          ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-1) * (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k
          ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-1) * (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k
          ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-1) * (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k
          ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))

def dDiffURowCoeff (M k : ℕ) : ℤ :=
  (∑ q ∈ (TIdx M).filter
      (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k),
      (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (∑ q ∈ (TIdx M).filter
        (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (TIdx M).filter (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (TIdx M).filter (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (TIdx M).filter (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (TIdx M).filter (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + 4 * (∑ q ∈ (TIdx M).filter (fun q => q.1.2 = k),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (TIdx M).filter (fun q => q.2.1 + q.2.2.2.1 = k),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + (-2) * (∑ q ∈ (TIdx M).filter (fun q => ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + 4 * (∑ q ∈ (TIdx M).filter (fun q => q.2.1 = k),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))
    + 4 * (∑ q ∈ (TIdx M).filter (fun q => q.2.2.2.1 = k),
        (q.1.2 : ℤ) * (q.2.1 : ℤ) * (q.2.2.2.1 : ℤ))

theorem dDiffRowCoeff_cast (M k j : ℕ) :
    ((dDiffRowCoeff M k j : ℤ) : K)
      = (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k
                ∧ q.1.2 = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k
                ∧ q.1.2 = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k
                ∧ q.1.2 = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k
                ∧ q.1.2 = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => q.1.2 = k
                ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => q.1.2 = k
                ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => q.1.2 = k
                ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => q.1.2 = k
                ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (4 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k ∧ q.2.2.2.1 = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (4 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter (fun q => q.2.2.2.1 = k ∧ q.2.1 = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k
                ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k
                ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k
                ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k
                ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k
                ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k
                ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k
                ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k
                ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) := by
  unfold dDiffRowCoeff
  rw [TIdx_eq]
  push_cast
  ring

theorem dDiffURowCoeff_cast (M k : ℕ) :
    ((dDiffURowCoeff M k : ℤ) : K)
      = (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (1 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (4 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter (fun q => q.2.1 + q.2.2.2.1 = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (-2 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter
              (fun q => ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (4 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
        + (4 : K) * (∑ q ∈ ((((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
            fun p => Sols (M - p.1)).filter (fun q => q.2.2.2.1 = k)),
          (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) := by
  unfold dDiffURowCoeff
  rw [TIdx_eq]
  push_cast
  ring

set_option maxHeartbeats 51200000 in

theorem dDiff_mixed_merge (u v : K) (M : ℕ) :
    (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k
                  ∧ q.1.2 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k
                  ∧ q.1.2 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k
                  ∧ q.1.2 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k
                  ∧ q.1.2 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k
                  ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k
                  ∧ ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k
                  ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => q.1.2 = k
                  ∧ ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (4 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k ∧ q.2.2.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (4 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter (fun q => q.2.2.2.1 = k ∧ q.2.1 = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      + (-1 : K) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k
                  ∧ ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = j),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz u (k : ℤ) * Fz v (j : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((dDiffRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dDiffRowCoeff_cast]
  ring

set_option maxHeartbeats 51200000 in

theorem dDiff_pure_merge (w : K) (M : ℕ) :
    (1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      + (1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      + (1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ))).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      + (1 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ))).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      + (-2 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      + (-2 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      + (-2 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      + (-2 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.1.2 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      + (4 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      + (-2 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter (fun q => q.2.1 + q.2.2.2.1 = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      + (-2 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter
                (fun q => ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      + (4 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      + (4 : K) * (∑ k ∈ Finset.Icc 1 M,
          (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma
              fun p => Sols (M - p.1)).filter (fun q => q.2.2.2.1 = k),
            (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K))
            * Fz w (k : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ((dDiffURowCoeff M k : ℤ) : K) * Fz w (k : ℤ) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dDiffURowCoeff_cast]
  ring

set_option maxHeartbeats 51200000 in

theorem groupDDiff_eq_bins [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (M : ℕ) :
    ∑ a ∈ Finset.Ico 1 M,
        (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
          * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
              (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            ((dDiffRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + 2 * (∑ k ∈ Finset.Icc 1 M, ((dDiffURowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + 2 * (∑ j ∈ Finset.Icc 1 M, ((dDiffURowCoeff M j : ℤ) : K) * Fz v (j : ℤ)) := by
  have h0 := groupD_cross_diffsq_distrib (u := u) (v := v) hu0 hv0 M
  have h1 := groupD_diffsq_eq_sum_lines (u := u) (v := v) hu0 hv0 M
  have h2 := groupD_diffsq_mixed_eq_sum_lines (K := K) u v M
  have h3u := groupD_diffsq_pure_eq_sum_lines (u := u) hu0 M
  have h3v := groupD_diffsq_pure_eq_sum_lines (u := v) hv0 M
  have h4 := dDiff_mixed_merge (K := K) u v M
  have h5u := dDiff_pure_merge (K := K) u M
  have h5v := dDiff_pure_merge (K := K) v M
  linear_combination h0 + h1 + h2 + 2 * h3u + 2 * h3v + h4 + 2 * h5u + 2 * h5v

end DiffsqBlock

section DSubAssembly

def dRowCoeff (M k j : ℕ) : ℤ :=
  2 * dTentRowCoeff M k j + 2 * dTentRowCoeff M j k + dDiffRowCoeff M k j
    + (-2) * dXColRowCoeff M k j + (-2) * dXColRowCoeff M j k

def dURowCoeff (M k : ℕ) : ℤ :=
  2 * dTentURowCoeff M k + 2 * dTentVRowCoeff M k + 2 * dDiffURowCoeff M k
    + (-2) * dXColVRowCoeff M k

def dVRowCoeff (M j : ℕ) : ℤ :=
  2 * dTentVRowCoeff M j + 2 * dTentURowCoeff M j + 2 * dDiffURowCoeff M j
    + (-2) * dXColVRowCoeff M j

theorem dRowCoeff_cast (M k j : ℕ) :
    ((dRowCoeff M k j : ℤ) : K)
      = 2 * ((dTentRowCoeff M k j : ℤ) : K) + 2 * ((dTentRowCoeff M j k : ℤ) : K)
        + ((dDiffRowCoeff M k j : ℤ) : K) + (-2) * ((dXColRowCoeff M k j : ℤ) : K)
        + (-2) * ((dXColRowCoeff M j k : ℤ) : K) := by
  unfold dRowCoeff
  push_cast
  ring

theorem dURowCoeff_cast (M k : ℕ) :
    ((dURowCoeff M k : ℤ) : K)
      = 2 * ((dTentURowCoeff M k : ℤ) : K) + 2 * ((dTentVRowCoeff M k : ℤ) : K)
        + 2 * ((dDiffURowCoeff M k : ℤ) : K) + (-2) * ((dXColVRowCoeff M k : ℤ) : K) := by
  unfold dURowCoeff
  push_cast
  ring

theorem dVRowCoeff_cast (M j : ℕ) :
    ((dVRowCoeff M j : ℤ) : K)
      = 2 * ((dTentVRowCoeff M j : ℤ) : K) + 2 * ((dTentURowCoeff M j : ℤ) : K)
        + 2 * ((dDiffURowCoeff M j : ℤ) : K) + (-2) * ((dXColVRowCoeff M j : ℤ) : K) := by
  unfold dVRowCoeff
  push_cast
  ring

set_option maxHeartbeats 51200000 in

theorem crossInterior_eq_sum_lines [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) (M : ℕ) :
    (∑ a ∈ Finset.Ico 1 M,
        ((xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
            * (2 * ((∑ e ∈ (M - a).divisors, (e : K) * tent u e)
                  + ∑ e ∈ (M - a).divisors, (e : K) * tent v e)
              + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                  (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))
          - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d)
              * xCoeff v (M - a))
          - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz u (d : ℤ) + 2) * tent v d)
              * xCoeff u (M - a))))
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            ((dRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ((dURowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + (∑ j ∈ Finset.Icc 1 M, ((dVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ)) := by

  have hTu := groupDTentU_eq_bins (u := u) (v := v) hu0 hu1 hv0 M
  have hTv := groupDTentV_eq_bins (u := u) (v := v) hu0 hv0 hv1 M
  have hDD := groupDDiff_eq_bins (u := u) (v := v) hu0 hv0 M
  have hXu := groupDXColU_eq_bins (u := u) (v := v) hu0 hu1 hv0 M
  have hXv := groupDXColV_eq_bins (u := u) (v := v) hu0 hv0 hv1 M

  have hsplit : (∑ a ∈ Finset.Ico 1 M,
        ((xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
            * (2 * ((∑ e ∈ (M - a).divisors, (e : K) * tent u e)
                  + ∑ e ∈ (M - a).divisors, (e : K) * tent v e)
              + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                  (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))
          - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d)
              * xCoeff v (M - a))
          - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz u (d : ℤ) + 2) * tent v d)
              * xCoeff u (M - a))))
      = 2 * (∑ a ∈ Finset.Ico 1 M,
            (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
              * (∑ e ∈ (M - a).divisors, (e : K) * tent u e))
        + (2 * (∑ a ∈ Finset.Ico 1 M,
            (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
              * (∑ e ∈ (M - a).divisors, (e : K) * tent v e))
        + ((∑ a ∈ Finset.Ico 1 M,
            (xCoeff (u * v) a + xCoeff (u * v⁻¹) a)
              * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i)
                  (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))
        + ((-2) * (∑ a ∈ Finset.Ico 1 M,
            (∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d)
              * xCoeff v (M - a))
        + (-2) * (∑ a ∈ Finset.Ico 1 M,
            (∑ d ∈ a.divisors, (d : K) * (Fz u (d : ℤ) + 2) * tent v d)
              * xCoeff u (M - a))))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring

  have hmix : 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((dTentRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((dTentRowCoeff M j k : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((dDiffRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-2) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((dXColRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (-2) * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((dXColRowCoeff M j k : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((dRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dRowCoeff_cast]
    ring

  have hubin : 2 * (∑ k ∈ Finset.Icc 1 M, ((dTentURowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + 2 * (∑ k ∈ Finset.Icc 1 M, ((dTentVRowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + 2 * (∑ k ∈ Finset.Icc 1 M, ((dDiffURowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + (-2) * (∑ k ∈ Finset.Icc 1 M, ((dXColVRowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ((dURowCoeff M k : ℤ) : K) * Fz u (k : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dURowCoeff_cast]
    ring

  have hvbin : 2 * (∑ j ∈ Finset.Icc 1 M, ((dTentVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ))
        + 2 * (∑ j ∈ Finset.Icc 1 M, ((dTentURowCoeff M j : ℤ) : K) * Fz v (j : ℤ))
        + 2 * (∑ j ∈ Finset.Icc 1 M, ((dDiffURowCoeff M j : ℤ) : K) * Fz v (j : ℤ))
        + (-2) * (∑ j ∈ Finset.Icc 1 M, ((dXColVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ))
      = ∑ j ∈ Finset.Icc 1 M, ((dVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dVRowCoeff_cast]
    ring
  linear_combination hsplit + 2 * hTu + 2 * hTv + hDD + (-2) * hXu + (-2) * hXv
    + hmix + hubin + hvbin

end DSubAssembly

section FullAssembly

def sumRowCoeff (M k j : ℕ) : ℤ :=
  intRowCoeff M k j + bdryRowCoeff M k j + dRowCoeff M k j

def sumURowCoeff (M k : ℕ) : ℤ :=
  intURowCoeff M k + bdryURowCoeff M k + dURowCoeff M k

def sumVRowCoeff (M j : ℕ) : ℤ :=
  intVRowCoeff M j + bdryVRowCoeff M j + dVRowCoeff M j

theorem sumRowCoeff_cast (M k j : ℕ) :
    ((sumRowCoeff M k j : ℤ) : K)
      = ((intRowCoeff M k j : ℤ) : K) + ((bdryRowCoeff M k j : ℤ) : K)
        + ((dRowCoeff M k j : ℤ) : K) := by
  unfold sumRowCoeff
  push_cast
  ring

theorem sumURowCoeff_cast (M k : ℕ) :
    ((sumURowCoeff M k : ℤ) : K)
      = ((intURowCoeff M k : ℤ) : K) + ((bdryURowCoeff M k : ℤ) : K)
        + ((dURowCoeff M k : ℤ) : K) := by
  unfold sumURowCoeff
  push_cast
  ring

theorem sumVRowCoeff_cast (M j : ℕ) :
    ((sumVRowCoeff M j : ℤ) : K)
      = ((intVRowCoeff M j : ℤ) : K) + ((bdryVRowCoeff M j : ℤ) : K)
        + ((dVRowCoeff M j : ℤ) : K) := by
  unfold sumVRowCoeff
  push_cast
  ring

set_option maxHeartbeats 51200000 in

theorem addDefectSumCoeff_eq_sum_lines [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M) :
    addDefectSumCoeff u v M
      = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
            ((sumRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ((sumURowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + (∑ j ∈ Finset.Icc 1 M, ((sumVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ)) := by
  have habs := addDefectSumCoeff_eq_absorbed (u := u) (v := v) hu0 hv0 hu1 hv1 huvm huvd hM
  have hint := interior_eq_sum_lines (u := u) (v := v) hu0 hv0 hu1 hv1 M
  have hbdry := boundaryOuter_eq_sum_lines (u := u) (v := v) hu0 hv0 hu1 hv1 hM
  have hD := crossInterior_eq_sum_lines (u := u) (v := v) hu0 hu1 hv0 hv1 M

  have hmix : (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((intRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((bdryRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((dRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
          ((sumRowCoeff M k j : ℤ) : K) * Fz u (k : ℤ) * Fz v (j : ℤ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sumRowCoeff_cast]
    ring

  have hubin : (∑ k ∈ Finset.Icc 1 M, ((intURowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ((bdryURowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
        + (∑ k ∈ Finset.Icc 1 M, ((dURowCoeff M k : ℤ) : K) * Fz u (k : ℤ))
      = ∑ k ∈ Finset.Icc 1 M, ((sumURowCoeff M k : ℤ) : K) * Fz u (k : ℤ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sumURowCoeff_cast]
    ring

  have hvbin : (∑ j ∈ Finset.Icc 1 M, ((intVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ))
        + (∑ j ∈ Finset.Icc 1 M, ((bdryVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ))
        + (∑ j ∈ Finset.Icc 1 M, ((dVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ))
      = ∑ j ∈ Finset.Icc 1 M, ((sumVRowCoeff M j : ℤ) : K) * Fz v (j : ℤ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sumVRowCoeff_cast]
    ring
  linear_combination habs + hint + hbdry + hD + hmix + hubin + hvbin

end FullAssembly

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve
p2m_export "TateCurve" "unitSpectator nnnorm_unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows symSumNum AddParams addDefectSum addDefectSum_eq_zero_iff addDefectSum_q_mul_left offLattice_of_norm_eq_one norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma cauchyMulInt Fz Gz Fz_natCast tent cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b a₄ a₆ curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C2_exports ks17_C3_exports ks17_D2_exports ks17_D3_exports"
p2m_open "TateCurve~SymAddHyps"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u v : K}

section RegionSwap

namespace ExpansionRegion p2m_export "TateCurve.ExpansionRegion" "div_hi params v_hi u_hi norm_q_lt_one div_lo mul_lo mul_hi u_lo v_lo" end ExpansionRegion
namespace ExpansionRegion
p2m_open_scoped "TateCurve.ExpansionRegion" in

private lemma _root_.TateCurve.ExpansionRegion.swap (h : ExpansionRegion q u v) : ExpansionRegion q v u := by
  have hu0 : u ≠ 0 := h.params.u_ne_zero
  have hv0 : v ≠ 0 := h.params.v_ne_zero
  have hd0 : u * v⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hv0)
  have hdpos : (0 : ℝ) < ‖u * v⁻¹‖ := norm_pos_iff.mpr hd0

  have hinv_norm : ‖v * u⁻¹‖ = ‖u * v⁻¹‖⁻¹ := by
    rw [show v * u⁻¹ = (u * v⁻¹)⁻¹ by rw [mul_inv_rev, inv_inv], norm_inv]
  refine ⟨h.params.swap, h.norm_q_lt_one, h.v_lo, h.v_hi, h.u_lo, h.u_hi, ?_, ?_, ?_, ?_⟩
  · rw [mul_comm v u]; exact h.mul_lo
  · rw [mul_comm v u]; exact h.mul_hi
  ·
    rw [hinv_norm, ← one_div, lt_div_iff₀ hdpos]
    exact h.div_hi
  ·
    rw [hinv_norm, ← div_eq_mul_inv, div_lt_one hdpos]
    exact h.div_lo

end ExpansionRegion
p2m_export "TateCurve" "ExpansionRegion.swap"
end RegionSwap

section SpectatorPairs

lemma unitSpectator_mul_ne_one (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) {n m : ℕ} (hnm : n ≠ m) :
    unitSpectator q n * unitSpectator q m ≠ 1 := by
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  intro hcon

  have hexp : q ^ (n + 1) * unitSpectator q m + q ^ (m + 1) = 0 := by
    have h1 : q ^ (n + 1) * unitSpectator q m + q ^ (m + 1)
        = unitSpectator q n * unitSpectator q m - 1 := by
      simp only [unitSpectator]; ring
    rw [h1, hcon, sub_self]

  have hna : ‖q ^ (n + 1) * unitSpectator q m‖₊ = ‖q‖₊ ^ (n + 1) := by
    rw [nnnorm_mul, nnnorm_pow, nnnorm_unitSpectator hq0 hq1 m, mul_one]
  have hnb : ‖q ^ (m + 1)‖₊ = ‖q‖₊ ^ (m + 1) := by rw [nnnorm_pow]
  have hpow_ne : ‖q‖ ^ (n + 1) ≠ ‖q‖ ^ (m + 1) := by
    rcases lt_or_gt_of_ne hnm with h | h
    · exact ne_of_gt (pow_lt_pow_right_of_lt_one₀ hqpos hq1 (by omega))
    · exact ne_of_lt (pow_lt_pow_right_of_lt_one₀ hqpos hq1 (by omega))
  have hne : ‖q ^ (n + 1) * unitSpectator q m‖₊ ≠ ‖q ^ (m + 1)‖₊ := by
    rw [hna, hnb]
    intro heq
    apply hpow_ne
    have hcoe := congrArg (fun x : ℝ≥0 => (x : ℝ)) heq
    simpa using hcoe

  have hmax := nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hne
  rw [hexp, nnnorm_zero] at hmax
  have hbne : ‖q ^ (m + 1)‖₊ ≠ 0 := fun hcon =>
    pow_ne_zero (m + 1) hq0 (nnnorm_eq_zero.mp hcon)
  have hbpos : (0 : ℝ≥0) < ‖q ^ (m + 1)‖₊ := lt_of_le_of_ne zero_le (Ne.symm hbne)
  exact absurd hmax.symm (ne_of_gt (lt_max_of_lt_right hbpos))

lemma expansionRegion_unitSpectator_pair (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) {n m : ℕ}
    (hnm : n ≠ m) :
    ExpansionRegion q (unitSpectator q n) (unitSpectator q m) := by
  have hn0 : unitSpectator q n ≠ 0 := unitSpectator_ne_zero hq0 hq1 n
  have hm0 : unitSpectator q m ≠ 0 := unitSpectator_ne_zero hq0 hq1 m
  have hnnorm : ‖unitSpectator q n‖ = 1 := norm_unitSpectator hq0 hq1 n
  have hmnorm : ‖unitSpectator q m‖ = 1 := norm_unitSpectator hq0 hq1 m
  have hmulnorm : ‖unitSpectator q n * unitSpectator q m‖ = 1 := by
    rw [norm_mul, hnnorm, hmnorm, mul_one]
  have hdivnorm : ‖unitSpectator q n * (unitSpectator q m)⁻¹‖ = 1 := by
    rw [norm_mul, norm_inv, hnnorm, hmnorm, inv_one, mul_one]
  have hmul1 : unitSpectator q n * unitSpectator q m ≠ 1 :=
    unitSpectator_mul_ne_one hq0 hq1 hnm
  have hdiv1 : unitSpectator q n * (unitSpectator q m)⁻¹ ≠ 1 := by
    intro hcon
    have heq : unitSpectator q n = unitSpectator q m := by
      have h1 : unitSpectator q n * (unitSpectator q m)⁻¹ * unitSpectator q m
          = 1 * unitSpectator q m := by rw [hcon]
      rwa [mul_assoc, inv_mul_cancel₀ hm0, mul_one, one_mul] at h1
    exact hnm (unitSpectator_injective hq0 hq1 heq)
  refine ⟨⟨hq0, hn0, hm0,
    offLattice_of_norm_eq_one hq0 hq1 hnnorm (unitSpectator_ne_one hq0 n),
    offLattice_of_norm_eq_one hq0 hq1 hmnorm (unitSpectator_ne_one hq0 m),
    offLattice_of_norm_eq_one hq0 hq1 hmulnorm hmul1,
    offLattice_of_norm_eq_one hq0 hq1 hdivnorm hdiv1⟩,
    hq1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnnorm]; exact hq1
  · rw [hnnorm, mul_one]; exact hq1
  · rw [hmnorm]; exact hq1
  · rw [hmnorm, mul_one]; exact hq1
  · rw [hmulnorm]; exact hq1
  · rw [hmulnorm, mul_one]; exact hq1
  · rw [hdivnorm]; exact hq1
  · rw [hdivnorm, mul_one]; exact hq1

end SpectatorPairs

section UFreeColumn

variable {B : ℝ} {d : ℕ} {t : ℕ → Finset ℤ} {w : ℕ → ℤ → K}

lemma norm_uFreeColumn_le (hB : 0 ≤ B)
    (hw : ∀ M j, ‖w M j‖ ≤ B * ((M : ℝ) + 1) ^ d) {z : K} (hz : ‖z‖ = 1) (M : ℕ) :
    ‖∑ j ∈ t M, w M j * z ^ j‖ ≤ B * ((M : ℝ) + 1) ^ d :=
  norm_finsetSum_mul_zpow_le_of_norm_eq_one hz
    (mul_nonneg hB (by positivity)) (fun j _ => hw M j)

lemma summable_uFreeColumn_mul_pow (hB : 0 ≤ B)
    (hw : ∀ M j, ‖w M j‖ ≤ B * ((M : ℝ) + 1) ^ d) {z : K} (hz : ‖z‖ = 1)
    {q' : K} (hq'0 : q' ≠ 0) (hq'1 : ‖q'‖ < 1) :
    Summable fun M : ℕ => (∑ j ∈ t M, w M j * z ^ j) * q' ^ M := by
  have hq'pos : (0 : ℝ) < ‖q'‖ := norm_pos_iff.mpr hq'0
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_)
    ((summable_polyGeomSeq d hq'pos hq'1).mul_left B))
  rw [norm_mul, norm_pow]
  calc ‖∑ j ∈ t M, w M j * z ^ j‖ * ‖q'‖ ^ M
      ≤ (B * ((M : ℝ) + 1) ^ d) * ‖q'‖ ^ M :=
        mul_le_mul_of_nonneg_right (norm_uFreeColumn_le hB hw hz M) (by positivity)
    _ = B * (((M : ℝ) + 1) ^ d * ‖q'‖ ^ M) := by ring

lemma sum_sub_ite_zero_mul_zpow {t : Finset ℤ} {w : ℤ → K} {C : K} (h0t : (0 : ℤ) ∈ t)
    (z : K) :
    ∑ j ∈ t, (w j - if j = 0 then C else 0) * z ^ j = (∑ j ∈ t, w j * z ^ j) - C := by
  classical
  calc ∑ j ∈ t, (w j - if j = 0 then C else 0) * z ^ j
      = ∑ j ∈ t, (w j * z ^ j - if j = 0 then C * z ^ j else 0) :=
        Finset.sum_congr rfl fun j _ => by
          by_cases hj : j = 0
          · rw [if_pos hj, if_pos hj]; ring
          · rw [if_neg hj, if_neg hj]; ring
    _ = (∑ j ∈ t, w j * z ^ j) - ∑ j ∈ t, (if j = 0 then C * z ^ j else 0) := by
        rw [Finset.sum_sub_distrib]
    _ = (∑ j ∈ t, w j * z ^ j) - C := by
        rw [Finset.sum_ite_eq' t 0 (fun j => C * z ^ j), if_pos h0t, zpow_zero, mul_one]

end UFreeColumn

section RowKill

variable {B : ℝ} {d : ℕ} {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
  {t : ℕ → Finset ℤ} {w : ℕ → ℤ → K}

theorem rows_eval_eq_zero_of_threeBin_envelope (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    (hB : 0 ≤ B)
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hw : ∀ M j, ‖w M j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hrow : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      addDefectSumCoeff u' v' M
        = ∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)
          + ∑ j ∈ t M, w M j * v' ^ j) :
    ∀ M k : ℕ, 1 ≤ k → k ≤ M → ∀ z : K, z ≠ 0 → ∑ j ∈ s M k, a M k j * z ^ j = 0 := by

  refine rows_eval_eq_zero_of_master_at_spectators_envelope hq0 hq1 hB ha ?_
  intro n
  have hsp_norm : ‖unitSpectator q n‖ = 1 := norm_unitSpectator hq0 hq1 n
  have hsp_ne1 : unitSpectator q n ≠ 1 := unitSpectator_ne_one hq0 n

  have hinv : ∀ q' w' : K, q' ≠ 0 → 1 < ‖w'‖ → ‖q'‖ * ‖w'‖ < 1 →
      (addDefectSum q' (q' * w') (unitSpectator q n)
        - ∑' M : ℕ, (∑ j ∈ t M, w M j * (unitSpectator q n) ^ j) * q' ^ M)
      = addDefectSum q' w' (unitSpectator q n)
        - ∑' M : ℕ, (∑ j ∈ t M, w M j * (unitSpectator q n) ^ j) * q' ^ M := by
    intro q' w' hq'0 _ _
    rw [addDefectSum_q_mul_left hq'0]
  refine master_of_hasSum_qshift_envelope hB (spectatorRows s a (unitSpectator q n))
    (fun N k => norm_finsetSum_mul_zpow_le_of_norm_eq_one hsp_norm
      (mul_nonneg hB (by positivity)) (fun j _ => ha N k j))
    (g := fun q' u' => addDefectSum q' u' (unitSpectator q n)
      - ∑' M : ℕ, (∑ j ∈ t M, w M j * (unitSpectator q n) ^ j) * q' ^ M)
    hinv ?_
  intro q' w' hq'0 hlo hhi hwne

  have hq'pos : (0 : ℝ) < ‖q'‖ := norm_pos_iff.mpr hq'0
  have hq'1 : ‖q'‖ < 1 := by nlinarith [norm_nonneg w']

  have hreg' : ExpansionRegion q' w' (unitSpectator q n) :=
    expansionRegion_of_spectator hq'0 hlo hhi hwne hsp_norm hsp_ne1

  have hqexp := addDefectSum_qExpansion hreg'
  have hUsum : Summable fun M : ℕ =>
      (∑ j ∈ t M, w M j * (unitSpectator q n) ^ j) * q' ^ M :=
    summable_uFreeColumn_mul_pow hB hw hsp_norm hq'0 hq'1

  have heq : (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M, spectatorRows s a (unitSpectator q n) M k
          * (w' ^ k + w'⁻¹ ^ k - 2)) * q' ^ M)
      = fun M : ℕ =>
        addDefectSumCoeff w' (unitSpectator q n) M * q' ^ M
          - (∑ j ∈ t M, w M j * (unitSpectator q n) ^ j) * q' ^ M := by
    funext M
    rw [hrow q' w' (unitSpectator q n) hreg' M]
    simp only [spectatorRows]
    ring
  rw [heq]
  exact hqexp.sub hUsum.hasSum

end RowKill

section Constancy

variable {B : ℝ} {d : ℕ} {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
  {t : ℕ → Finset ℤ} {w : ℕ → ℤ → K}

theorem uFreeColumn_eval_eq_zero_of_threeBin_envelope (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    (hkill : ∀ M k : ℕ, 1 ≤ k → k ≤ M → ∀ z : K, z ≠ 0 → ∑ j ∈ s M k, a M k j * z ^ j = 0)
    (hrow : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      addDefectSumCoeff u' v' M
        = ∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)
          + ∑ j ∈ t M, w M j * v' ^ j)
    (h0t : ∀ M : ℕ, (0 : ℤ) ∈ t M)
    (hone : ∀ M : ℕ, ∑ j ∈ t M, w M j = 0) :
    ∀ M : ℕ, ∀ z : K, z ≠ 0 → ∑ j ∈ t M, w M j * z ^ j = 0 := by
  classical
  intro M

  have hcoeff : ∀ q' u' v' : K, ExpansionRegion q' u' v' →
      addDefectSumCoeff u' v' M = ∑ j ∈ t M, w M j * v' ^ j := by
    intro q' u' v' hreg
    rw [hrow q' u' v' hreg M]
    have hzero : ∑ k ∈ Finset.Icc 1 M,
        (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' := Finset.mem_Icc.mp hk
      rw [hkill M k hk'.1 hk'.2 v' hreg.params.v_ne_zero, zero_mul]
    rw [hzero, zero_add]

  have hpair : ∀ n m : ℕ, n ≠ m →
      ∑ j ∈ t M, w M j * (unitSpectator q m) ^ j
        = ∑ j ∈ t M, w M j * (unitSpectator q n) ^ j := by
    intro n m hnm
    have hregnm := expansionRegion_unitSpectator_pair hq0 hq1 hnm
    have hregmn := expansionRegion_unitSpectator_pair hq0 hq1 (Ne.symm hnm)
    have hdiv1 : unitSpectator q n * (unitSpectator q m)⁻¹ ≠ 1 := by
      intro hcon
      have heq : unitSpectator q n = unitSpectator q m := by
        have h1 : unitSpectator q n * (unitSpectator q m)⁻¹ * unitSpectator q m
            = 1 * unitSpectator q m := by rw [hcon]
        rwa [mul_assoc, inv_mul_cancel₀ (unitSpectator_ne_zero hq0 hq1 m), mul_one,
          one_mul] at h1
      exact hnm (unitSpectator_injective hq0 hq1 heq)
    have hswap : addDefectSumCoeff (unitSpectator q m) (unitSpectator q n) M
        = addDefectSumCoeff (unitSpectator q n) (unitSpectator q m) M :=
      addDefectSumCoeff_swap (unitSpectator_ne_zero hq0 hq1 n)
        (unitSpectator_ne_zero hq0 hq1 m) hdiv1 M
    calc ∑ j ∈ t M, w M j * (unitSpectator q m) ^ j
        = addDefectSumCoeff (unitSpectator q n) (unitSpectator q m) M :=
          (hcoeff q _ _ hregnm).symm
      _ = addDefectSumCoeff (unitSpectator q m) (unitSpectator q n) M := hswap.symm
      _ = ∑ j ∈ t M, w M j * (unitSpectator q n) ^ j := hcoeff q _ _ hregmn

  set C : K := ∑ j ∈ t M, w M j * (unitSpectator q 0) ^ j with hC

  have hvan : ∀ z : K, z ≠ 0 →
      ∑ j ∈ t M, (w M j - if j = 0 then C else 0) * z ^ j = 0 := by
    refine laurent_eval_eq_zero_of_infinite_roots
      (S := Set.range fun m : ℕ => unitSpectator q (m + 1))
      (Set.infinite_range_of_injective fun a b hab => by
        have hinj := unitSpectator_injective hq0 hq1 hab
        omega) ?_ ?_
    · rintro z ⟨m, rfl⟩
      exact unitSpectator_ne_zero hq0 hq1 (m + 1)
    · rintro z ⟨m, rfl⟩
      rw [sum_sub_ite_zero_mul_zpow (h0t M), hpair 0 (m + 1) (by omega), ← hC, sub_self]

  have hC0 : C = 0 := by
    have h1 := hvan 1 one_ne_zero
    rw [sum_sub_ite_zero_mul_zpow (h0t M)] at h1
    have hone' : ∑ j ∈ t M, w M j * (1 : K) ^ j = 0 :=
      calc ∑ j ∈ t M, w M j * (1 : K) ^ j
          = ∑ j ∈ t M, w M j := Finset.sum_congr rfl fun j _ => by rw [one_zpow, mul_one]
        _ = 0 := hone M
    rw [hone', zero_sub, neg_eq_zero] at h1
    exact h1

  intro z hz
  have h1 := hvan z hz
  rw [sum_sub_ite_zero_mul_zpow (h0t M), hC0, sub_zero] at h1
  exact h1

end Constancy

section Composition

variable {B : ℝ} {d : ℕ} {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
  {t : ℕ → Finset ℤ} {w : ℕ → ℤ → K}

theorem symAdd_sum_regional_of_threeBin_envelope (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    (hB : 0 ≤ B)
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hw : ∀ M j, ‖w M j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hrow : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      addDefectSumCoeff u' v' M
        = ∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)
          + ∑ j ∈ t M, w M j * v' ^ j)
    (h0t : ∀ M : ℕ, (0 : ℤ) ∈ t M)
    (hone : ∀ M : ℕ, ∑ j ∈ t M, w M j = 0) :
    ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v') := by

  have hkill := rows_eval_eq_zero_of_threeBin_envelope hq0 hq1 hB ha hw hrow
  have hUzero := uFreeColumn_eval_eq_zero_of_threeBin_envelope hq0 hq1 hkill hrow h0t hone
  intro u' v' hreg

  have hcoeff : ∀ M : ℕ, addDefectSumCoeff u' v' M = 0 := by
    intro M
    rw [hrow q u' v' hreg M]
    have hzero1 : ∑ k ∈ Finset.Icc 1 M,
        (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' := Finset.mem_Icc.mp hk
      rw [hkill M k hk'.1 hk'.2 v' hreg.params.v_ne_zero, zero_mul]
    rw [hzero1, zero_add, hUzero M v' hreg.params.v_ne_zero]

  have hqexp := addDefectSum_qExpansion hreg
  have hfun : (fun M : ℕ => addDefectSumCoeff u' v' M * q ^ M) = fun _ => (0 : K) := by
    funext M
    rw [hcoeff M, zero_mul]
  rw [hfun] at hqexp
  exact addDefectSum_eq_zero_iff.mp (hqexp.unique hasSum_zero)

end Composition

section AllParams

variable [CharZero K] [DecidableEq K]
variable {B : ℝ} {d : ℕ} {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
  {t : ℕ → Finset ℤ} {w : ℕ → ℤ → K} {τ : K}

theorem symAdd_sum_allAddParams_of_threeBin_envelope (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    (hτ : τ ^ 2 = q) (hB : 0 ≤ B)
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hw : ∀ M j, ‖w M j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hrow : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      addDefectSumCoeff u' v' M
        = ∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)
          + ∑ j ∈ t M, w M j * v' ^ j)
    (h0t : ∀ M : ℕ, (0 : ℤ) ∈ t M)
    (hone : ∀ M : ℕ, ∑ j ∈ t M, w M j = 0)
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) :=
  symAdd_sum_of_region_closed hq0 hq1 hτ
    (symAdd_sum_regional_of_threeBin_envelope hq0 hq1 hB ha hw hrow h0t hone) hregD1 hp

theorem symAdd_sum_allAddParams_of_threeBin_envelope_isAlgClosed [IsAlgClosed K]
    (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) (hB : 0 ≤ B)
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hw : ∀ M j, ‖w M j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hrow : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      addDefectSumCoeff u' v' M
        = ∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)
          + ∑ j ∈ t M, w M j * v' ^ j)
    (h0t : ∀ M : ℕ, (0 : ℤ) ∈ t M)
    (hone : ∀ M : ℕ, ∑ j ∈ t M, w M j = 0)
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v'))) :
    ∀ u' v' : K, AddParams q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v') := by
  obtain ⟨τ, hτ⟩ := exists_sqrt_of_isAlgClosed (K := K) q
  exact fun u' v' hp =>
    symAdd_sum_allAddParams_of_threeBin_envelope hq0 hq1 hτ hB ha hw hrow h0t hone hregD1 hp

end AllParams

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Finset

namespace TateCurve
p2m_export "TateCurve" "unitSpectator nnnorm_unitSpectator norm_unitSpectator unitSpectator_ne_zero unitSpectator_ne_one unitSpectator_injective laurent_eval_eq_zero_of_infinite_roots spectatorRows symSumNum AddParams addDefectSum addDefectSum_eq_zero_iff addDefectSum_q_mul_left offLattice_of_norm_eq_one norm_finsetSum_mul_zpow_le_of_norm_eq_one specTail specAlpha specGamma cauchyMulInt Fz Gz Fz_natCast tent cauchyMul xCoeffFull a₄Coeff a₆Coeff xfun yfun pointX pointY term b a₄ a₆ curve xDivTerm xCoeff addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff cauchyMulIntTriple psiCoeffFull addDefectDiffCoeff svComplex LatticeRep OnHalfLattice ks17_A_exports ks17_B_exports ks17_C1_exports ks17_C2_exports ks17_C3_exports ks17_D2_exports ks17_D3_exports"
p2m_open "TateCurve~SymAddHyps"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u v : K}

section MonomialConversion

theorem Fz_one (a : ℤ) : Fz (1 : K) a = 0 := by
  unfold Fz
  rw [one_zpow, one_zpow]
  ring

def s1PosSupport (M : ℕ) : Finset ℤ := (Finset.Icc 1 M).image ((↑·) : ℕ → ℤ)

def s1MonoSupport (M : ℕ) : Finset ℤ :=
  insert 0 (s1PosSupport M ∪ (s1PosSupport M).image (fun j => -j))

theorem s1PosSupport_subset (M : ℕ) : s1PosSupport M ⊆ s1MonoSupport M :=
  Finset.subset_union_left.trans (Finset.subset_insert 0 _)

theorem zero_mem_s1MonoSupport (M : ℕ) : (0 : ℤ) ∈ s1MonoSupport M :=
  Finset.mem_insert_self 0 _

theorem s1MonoSupport_image_neg (M : ℕ) :
    (s1MonoSupport M).image (fun j => -j) = s1MonoSupport M := by
  unfold s1MonoSupport
  rw [Finset.image_insert, Finset.image_union, Finset.image_image]
  have h1 : (s1PosSupport M).image ((fun j : ℤ => -j) ∘ fun j : ℤ => -j) = s1PosSupport M := by
    rw [show ((fun j : ℤ => -j) ∘ fun j : ℤ => -j) = id by funext j; simp, Finset.image_id]
  rw [h1, neg_zero, Finset.union_comm]

def fzMonoCoeff (M : ℕ) (c : ℕ → ℤ) (C : ℤ) (j : ℤ) : ℤ :=
  (if j ∈ s1PosSupport M then c j.toNat else 0)
    + (if -j ∈ s1PosSupport M then c (-j).toNat else 0)
    + (if j = 0 then C - 2 * ∑ n ∈ Finset.Icc 1 M, c n else 0)

theorem sum_fzMonoCoeff_zpow (M : ℕ) (c : ℕ → ℤ) (C : ℤ) (z : K) :
    ∑ j ∈ s1MonoSupport M, ((fzMonoCoeff M c C j : ℤ) : K) * z ^ j
      = ∑ n ∈ Finset.Icc 1 M, ((c n : ℤ) : K) * Fz z (n : ℤ) + ((C : ℤ) : K) := by
  have hsub : s1PosSupport M ⊆ s1MonoSupport M := s1PosSupport_subset M

  have hsplit : ∀ j ∈ s1MonoSupport M, ((fzMonoCoeff M c C j : ℤ) : K) * z ^ j
      = (if j ∈ s1PosSupport M then ((c j.toNat : ℤ) : K) else 0) * z ^ j
        + (if -j ∈ s1PosSupport M then ((c (-j).toNat : ℤ) : K) else 0) * z ^ j
        + (if j = 0 then ((C : ℤ) : K) - 2 * ∑ n ∈ Finset.Icc 1 M, ((c n : ℤ) : K) else 0)
            * z ^ j := by
    intro j _
    unfold fzMonoCoeff
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib]

  have hfst : ∑ j ∈ s1MonoSupport M,
      (if j ∈ s1PosSupport M then ((c j.toNat : ℤ) : K) else 0) * z ^ j
      = ∑ n ∈ Finset.Icc 1 M, ((c n : ℤ) : K) * z ^ (n : ℤ) := by
    rw [Finset.sum_congr rfl (fun j _ => by rw [ite_mul, zero_mul]),
      Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    unfold s1PosSupport
    rw [Finset.sum_image (fun x _ y _ h => Nat.cast_injective h)]
    exact Finset.sum_congr rfl fun n _ => by rw [Int.toNat_natCast]

  have hsnd : ∑ j ∈ s1MonoSupport M,
      (if -j ∈ s1PosSupport M then ((c (-j).toNat : ℤ) : K) else 0) * z ^ j
      = ∑ n ∈ Finset.Icc 1 M, ((c n : ℤ) : K) * z ^ (-(n : ℤ)) := by
    have hinj : ∀ x ∈ s1MonoSupport M, ∀ y ∈ s1MonoSupport M,
        (fun j : ℤ => -j) x = (fun j : ℤ => -j) y → x = y := fun x _ y _ h => by
      simpa using h
    calc ∑ j ∈ s1MonoSupport M,
          (if -j ∈ s1PosSupport M then ((c (-j).toNat : ℤ) : K) else 0) * z ^ j
        = ∑ j ∈ (s1MonoSupport M).image (fun j => -j),
            (if -j ∈ s1PosSupport M then ((c (-j).toNat : ℤ) : K) else 0) * z ^ j := by
          rw [s1MonoSupport_image_neg]
      _ = ∑ j ∈ s1MonoSupport M,
            (if -(-j) ∈ s1PosSupport M then ((c (-(-j)).toNat : ℤ) : K) else 0) * z ^ (-j) :=
          Finset.sum_image hinj
      _ = ∑ j ∈ s1MonoSupport M,
            (if j ∈ s1PosSupport M then ((c j.toNat : ℤ) : K) else 0) * z ^ (-j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [neg_neg]
      _ = ∑ j ∈ s1PosSupport M, ((c j.toNat : ℤ) : K) * z ^ (-j) := by
          rw [Finset.sum_congr rfl (fun j _ => by rw [ite_mul, zero_mul]),
            Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
      _ = ∑ n ∈ Finset.Icc 1 M, ((c n : ℤ) : K) * z ^ (-(n : ℤ)) := by
          unfold s1PosSupport
          rw [Finset.sum_image (fun x _ y _ h => Nat.cast_injective h)]
          exact Finset.sum_congr rfl fun n _ => by rw [Int.toNat_natCast]

  have htrd : ∑ j ∈ s1MonoSupport M,
      (if j = 0 then ((C : ℤ) : K) - 2 * ∑ n ∈ Finset.Icc 1 M, ((c n : ℤ) : K) else 0) * z ^ j
      = ((C : ℤ) : K) - 2 * ∑ n ∈ Finset.Icc 1 M, ((c n : ℤ) : K) := by
    rw [Finset.sum_congr rfl (fun j _ => by rw [ite_mul, zero_mul]), Finset.sum_ite_eq']
    rw [if_pos (zero_mem_s1MonoSupport M), zpow_zero, mul_one]
  rw [hfst, hsnd, htrd]

  have hFz : ∀ n ∈ Finset.Icc 1 M, ((c n : ℤ) : K) * Fz z (n : ℤ)
      = ((c n : ℤ) : K) * z ^ (n : ℤ) + ((c n : ℤ) : K) * z ^ (-(n : ℤ))
        - 2 * ((c n : ℤ) : K) := fun n _ => by
    unfold Fz
    ring
  rw [Finset.sum_congr rfl hFz, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

theorem sum_fzMonoCoeff_eq_zero (M : ℕ) (c : ℕ → ℤ) :
    ∑ j ∈ s1MonoSupport M, ((fzMonoCoeff M c 0 j : ℤ) : K) = 0 := by
  have h1 : ∀ j ∈ s1MonoSupport M, ((fzMonoCoeff M c 0 j : ℤ) : K)
      = ((fzMonoCoeff M c 0 j : ℤ) : K) * (1 : K) ^ j := fun j _ => by
    rw [one_zpow, mul_one]
  rw [Finset.sum_congr rfl h1, sum_fzMonoCoeff_zpow]
  rw [Finset.sum_congr rfl (fun n _ => by rw [Fz_one, mul_zero])]
  simp

end MonomialConversion

section RowIdentity

private theorem region_side_conditions_S1Final {q' u' v' : K} (hreg : ExpansionRegion q' u' v') :
    u' ≠ 0 ∧ v' ≠ 0 ∧ u' ≠ 1 ∧ v' ≠ 1 ∧ u' * v' ≠ 1 ∧ u' * v'⁻¹ ≠ 1 := by
  refine ⟨hreg.params.u_ne_zero, hreg.params.v_ne_zero, ?_, ?_, ?_, ?_⟩
  · have h := hreg.params.offLattice_u 0
    rwa [zpow_zero, one_mul] at h
  · have h := hreg.params.offLattice_v 0
    rwa [zpow_zero, one_mul] at h
  · have h := hreg.params.offLattice_mul 0
    rwa [zpow_zero, one_mul] at h
  · have h := hreg.params.offLattice_div 0
    rwa [zpow_zero, one_mul] at h

theorem addDefectSumCoeff_eq_threeBin [CharZero K] {q' u' v' : K}
    (hreg : ExpansionRegion q' u' v') (M : ℕ) :
    addDefectSumCoeff u' v' M
      = ∑ k ∈ Finset.Icc 1 M,
          (∑ j ∈ s1MonoSupport M,
            ((fzMonoCoeff M (sumRowCoeff M k) (sumURowCoeff M k) j : ℤ) : K) * v' ^ j)
            * (u' ^ k + u'⁻¹ ^ k - 2)
        + ∑ j ∈ s1MonoSupport M, ((fzMonoCoeff M (sumVRowCoeff M) 0 j : ℤ) : K) * v' ^ j := by
  obtain ⟨hu0, hv0, hu1, hv1, hm, hd⟩ := region_side_conditions_S1Final hreg

  have hconv1 : ∀ k : ℕ, ∑ j ∈ s1MonoSupport M,
      ((fzMonoCoeff M (sumRowCoeff M k) (sumURowCoeff M k) j : ℤ) : K) * v' ^ j
      = ∑ n ∈ Finset.Icc 1 M, ((sumRowCoeff M k n : ℤ) : K) * Fz v' (n : ℤ)
        + ((sumURowCoeff M k : ℤ) : K) := fun k =>
    sum_fzMonoCoeff_zpow M (sumRowCoeff M k) (sumURowCoeff M k) v'
  have hconv2 : ∑ j ∈ s1MonoSupport M, ((fzMonoCoeff M (sumVRowCoeff M) 0 j : ℤ) : K) * v' ^ j
      = ∑ n ∈ Finset.Icc 1 M, ((sumVRowCoeff M n : ℤ) : K) * Fz v' (n : ℤ) := by
    rw [sum_fzMonoCoeff_zpow M (sumVRowCoeff M) 0 v']
    norm_num
  rcases Nat.eq_zero_or_pos M with rfl | hM
  ·
    rw [addDefectSumCoeff_zero hu0 hv0 hu1 hv1 hm hd, hconv2]
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) by rfl]
    simp
  ·
    rw [addDefectSumCoeff_eq_sum_lines hu0 hv0 hu1 hv1 hm hd hM, hconv2]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hconv1 k, ← Fz_natCast u' k, add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring

end RowIdentity

section Headline

variable [CharZero K]

theorem symAdd_sum_regional_E17 (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v') := by
  refine symAdd_sum_regional_of_threeBin_envelope (B := 1) (d := 0)
    (s := fun M _ => s1MonoSupport M)
    (a := fun M k j => ((fzMonoCoeff M (sumRowCoeff M k) (sumURowCoeff M k) j : ℤ) : K))
    (t := fun M => s1MonoSupport M)
    (w := fun M j => ((fzMonoCoeff M (sumVRowCoeff M) 0 j : ℤ) : K))
    hq0 hq1 zero_le_one ?_ ?_ ?_ ?_ ?_
  ·
    intro M k j
    simpa using norm_intCast_le_one K _
  ·
    intro M j
    simpa using norm_intCast_le_one K _
  ·
    intro q' u' v' hreg M
    exact addDefectSumCoeff_eq_threeBin hreg M
  ·
    intro M
    exact zero_mem_s1MonoSupport M
  ·
    intro M
    exact sum_fzMonoCoeff_eq_zero M (sumVRowCoeff M)

end Headline

section AllParams

variable [CharZero K] [DecidableEq K]
variable {τ : K}

theorem symAdd_sum_allParams_of_regional_D1 (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v'))) :
    ∀ u' v' : K, AddParams q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v') :=
  fun _ _ hp =>
    symAdd_sum_of_region_closed hq0 hq1 hτ (symAdd_sum_regional_E17 hq0 hq1) hregD1 hp

theorem symAdd_sum_allParams_of_regional_D1_of_isAlgClosed [IsAlgClosed K]
    (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v'))) :
    ∀ u' v' : K, AddParams q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v') := by
  obtain ⟨τ, hτ⟩ := exists_sqrt_of_isAlgClosed (K := K) q
  exact symAdd_sum_allParams_of_regional_D1 hq0 hq1 hτ hregD1

end AllParams

end TateCurve

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] {q : K} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    ∀ u' v' : K, TateCurve.ExpansionRegion q u' v' →
      (TateCurve.pointX q (u' * v') + TateCurve.pointX q (u' * v'⁻¹)) * (TateCurve.pointX q u' - TateCurve.pointX q v') ^ 2 =
        TateCurve.symSumNum q (TateCurve.pointX q u') (TateCurve.pointX q v') :=
  TateCurve.symAdd_sum_regional_E17 hq0 hq1

end S_TateCurve_symAdd_sum_regional
end P2MW
export P2MW.S_TateCurve_symAdd_sum_regional (solution)
