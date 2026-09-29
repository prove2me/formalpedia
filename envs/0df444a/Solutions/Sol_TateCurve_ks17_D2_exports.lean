-- Prove2me | solution 1 for TateCurve.ks17_D2_exports
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b716432d-927a-586a-8825-4354050a971a

import Mathlib
import Definitions.Def_TateCurve_XMultDistinctRouteB
import Definitions.Def_TateCurve_KeystoneVocab
import Theorems.Thm_TateCurve_ks17_A_exports
import Theorems.Thm_TateCurve_pointX_inv
import Theorems.Thm_TateCurve_pointX_zpow_mul
import Theorems.Thm_TateCurve_pointY_inv
import Theorems.Thm_TateCurve_pointY_zpow_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_ks17_D2_exports

set_option linter.unusedSectionVars false

open scoped NNReal
p2m_open "TateCurve P2MW.S_TateCurve_ks17_D2_exports.TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset"

universe u_1 u_2
namespace TateCurve
p2m_export "TateCurve" "eq_or_mul_eq_one_of_pointX_eq nsmul_prime_eq_zero SymAddHyps nonsingular_point SymAddHyps.sum symSumNum symSumNum_comm symSumNum_eq_b symProdNum_eq_b OffLattice OffLattice.zpow_mul OffLattice.q_mul OffLattice.inv AddParams addDefectSum offLattice_of_norm_eq_one xfun yfun pointX pointY b a₆ curve curve_a₁ curve_a₃ pointX_inv pointX_zpow_mul equation_pointX_pointY pointY_inv pointY_zpow_mul addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation ks17_A_exports"
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

namespace AddParams p2m_export "TateCurve.AddParams" "swap v_ne_zero u_ne_zero offLattice_v q_ne_zero offLattice_div offLattice_u offLattice_mul" end AddParams
namespace AddParams
p2m_open_scoped "TateCurve.AddParams" in
private theorem _root_.TateCurve.AddParams.latticeRep : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} {u' v' : K} (hp : AddParams q u v)
    (hu' : LatticeRep q u u') (hv' : LatticeRep q v v'),
      AddParams q u' v' :=
  TateCurve.ks17_A_exports.{u_1}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end AddParams
p2m_export "TateCurve" "AddParams.latticeRep"
end TateCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ a₆ Affine.nonsingular_add toAffine ψ₂ Affine.Y_eq_of_X_eq j Affine.addX_add_addX_negY_mul_sq' Affine.addX_mul_addX_negY_mul_sq"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "negY slope Point.some Point.some.injEq Nonsingular nonsingular_add Point addX nonsingular_neg Point.some_ne_zero addY Y_eq_of_X_eq Point.add_of_X_ne Point.neg_some addX_add_addX_negY_mul_sq' addX_mul_sq_of_X_ne addX_mul_addX_negY_mul_sq"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

lemma addX_sub_addX_negY_mul_sq {F : Type*} [Field F] {W : WeierstrassCurve F} [DecidableEq F]
    {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ ≠ x₂) :
    (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) -
        W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) *
        (x₁ - x₂) ^ 2 =
      -((y₁ - W.toAffine.negY x₁ y₁) * (y₂ - W.toAffine.negY x₂ y₂)) := by
  have e₁ := addX_mul_sq_of_X_ne (W := W.toAffine) y₁ y₂ hx
  have e₂ := addX_mul_sq_of_X_ne (W := W.toAffine) y₁ (W.toAffine.negY x₂ y₂) hx
  rw [sub_mul, e₁, e₂]
  simp only [negY]
  ring

end WeierstrassCurve.Affine

set_option linter.unusedSectionVars false

p2m_open "WeierstrassCurve.Affine P2MW.S_TateCurve_ks17_D2_exports.WeierstrassCurve.Affine"

namespace TateCurve
p2m_export "TateCurve" "eq_or_mul_eq_one_of_pointX_eq nsmul_prime_eq_zero SymAddHyps nonsingular_point SymAddHyps.sum symSumNum symSumNum_comm symSumNum_eq_b symProdNum_eq_b OffLattice OffLattice.zpow_mul OffLattice.q_mul OffLattice.inv AddParams addDefectSum offLattice_of_norm_eq_one xfun yfun pointX pointY b a₆ curve curve_a₁ curve_a₃ pointX_inv pointX_zpow_mul equation_pointX_pointY pointY_inv pointY_zpow_mul addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation ks17_A_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v w : K}

private lemma point_some_congr_MT {W : WeierstrassCurve K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

lemma point_inv_eq_neg (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : OffLattice q u)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q u⁻¹) (pointY q u⁻¹))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u)) :
    (Point.some (pointX q u⁻¹) (pointY q u⁻¹) h₁ : (curve q).toAffine.Point)
      = -Point.some (pointX q u) (pointY q u) h₂ := by
  rw [Point.neg_some]
  refine point_some_congr_MT (pointX_inv hq0 hu0 hu) ?_ h₁ _
  rw [pointY_inv hq0 hq hu0 hu, negY]
  show -pointY q u - pointX q u = -pointY q u - (curve q).a₁ * pointX q u - (curve q).a₃
  rw [curve_a₁, curve_a₃]
  ring

theorem point_mul_eq_add_or_sub_of_symAddHyps (hyps : SymAddHyps q)
    (hp : AddParams q v w) (hxne : pointX q v ≠ pointX q w)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (v * w)) (pointY q (v * w)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w)) :
    (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
        = Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃ ∨
      (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
        = -(Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃) ∨
      (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
        = Point.some (pointX q v) (pointY q v) h₂ - Point.some (pointX q w) (pointY q w) h₃ ∨
      (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
        = -(Point.some (pointX q v) (pointY q v) h₂ - Point.some (pointX q w) (pointY q w) h₃) := by
  have hd2 : (pointX q v - pointX q w) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hxne)

  have hS1 := hyps.sum v w hp
  have hS2 := hyps.prod v w hp
  rw [symSumNum_eq_b] at hS1
  rw [symProdNum_eq_b] at hS2

  have hsum := WeierstrassCurve.Affine.addX_add_addX_negY_mul_sq' (W := curve q)
    h₂.left h₃.left hxne
  have hprod := WeierstrassCurve.Affine.addX_mul_addX_negY_mul_sq (W := (curve q).toAffine)
    h₂.left h₃.left hxne

  have hsumEq : pointX q (v * w) + pointX q (v * w⁻¹) =
      (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w)) +
        (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v)
            ((curve q).toAffine.negY (pointX q w) (pointY q w))) :=
    mul_right_cancel₀ hd2 (hS1.trans hsum.symm)
  have hprodEq : pointX q (v * w) * pointX q (v * w⁻¹) =
      (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w)) *
        (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v)
            ((curve q).toAffine.negY (pointX q w) (pointY q w))) :=
    mul_right_cancel₀ hd2 (hS2.trans hprod.symm)

  have hroot : (pointX q (v * w) -
        (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w))) *
      (pointX q (v * w) -
        (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v)
            ((curve q).toAffine.negY (pointX q w) (pointY q w)))) = 0 := by
    linear_combination pointX q (v * w) * hsumEq - hprodEq
  have hcond : ¬(pointX q v = pointX q w ∧
      pointY q v = (curve q).toAffine.negY (pointX q w) (pointY q w)) :=
    fun hxy => hxne hxy.left
  have hcond' : ¬(pointX q v = pointX q w ∧
      pointY q v = (curve q).toAffine.negY (pointX q w)
        ((curve q).toAffine.negY (pointX q w) (pointY q w))) :=
    fun hxy => hxne hxy.left
  rcases mul_eq_zero.mp hroot with hcase | hcase
  ·
    have hxeq := sub_eq_zero.mp hcase
    have hns : (curve q).toAffine.Nonsingular
        ((curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w)))
        ((curve q).toAffine.addY (pointX q v) (pointX q w) (pointY q v)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w))) :=
      WeierstrassCurve.Affine.nonsingular_add h₂ h₃ hcond
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.left hns.left hxeq with hyeq | hyeq
    · left
      rw [Point.add_of_X_ne hxne]
      exact point_some_congr_MT hxeq hyeq h₁ _
    · right; left
      rw [Point.add_of_X_ne hxne, Point.neg_some]
      exact point_some_congr_MT hxeq hyeq h₁ _
  ·
    have hxeq := sub_eq_zero.mp hcase
    have hns : (curve q).toAffine.Nonsingular
        ((curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v)
            ((curve q).toAffine.negY (pointX q w) (pointY q w))))
        ((curve q).toAffine.addY (pointX q v) (pointX q w) (pointY q v)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v)
            ((curve q).toAffine.negY (pointX q w) (pointY q w)))) :=
      WeierstrassCurve.Affine.nonsingular_add h₂ ((nonsingular_neg _ _).mpr h₃) hcond'
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.left hns.left hxeq with hyeq | hyeq
    · right; right; left
      rw [sub_eq_add_neg, Point.neg_some, Point.add_of_X_ne hxne]
      exact point_some_congr_MT hxeq hyeq h₁ _
    · right; right; right
      rw [sub_eq_add_neg, Point.neg_some, Point.add_of_X_ne hxne, Point.neg_some]
      exact point_some_congr_MT hxeq hyeq h₁ _

end TateCurve

set_option linter.unusedSectionVars false

p2m_open "WeierstrassCurve.Affine P2MW.S_TateCurve_ks17_D2_exports.WeierstrassCurve.Affine"

namespace TateCurve
p2m_export "TateCurve" "eq_or_mul_eq_one_of_pointX_eq nsmul_prime_eq_zero SymAddHyps nonsingular_point SymAddHyps.sum symSumNum symSumNum_comm symSumNum_eq_b symProdNum_eq_b OffLattice OffLattice.zpow_mul OffLattice.q_mul OffLattice.inv AddParams addDefectSum offLattice_of_norm_eq_one xfun yfun pointX pointY b a₆ curve curve_a₁ curve_a₃ pointX_inv pointX_zpow_mul equation_pointX_pointY pointY_inv pointY_zpow_mul addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation ks17_A_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v w ζ : K} {p : ℕ}

private lemma point_some_congr_MB {W : WeierstrassCurve K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

lemma diffHyp_iff_addDefectDiff_eq_zero :
    DiffHyp q ↔ ∀ u v : K, AddParams q u v → addDefectDiff q u v = 0 := by
  constructor
  · intro h u v hp
    exact addDefectDiff_eq_zero_iff'.mpr (h u v hp)
  · intro h u v hp
    exact addDefectDiff_eq_zero_iff'.mp (h u v hp)

private lemma muT_norm_eq_one_of_isPrimitiveRoot_MB (hζ : IsPrimitiveRoot ζ p) (hp0 : p ≠ 0) :
    ‖ζ‖ = 1 := by
  have h1 : ‖ζ‖ ^ p = 1 := by rw [← norm_pow, hζ.pow_eq_one, norm_one]
  rcases (pow_eq_one_iff_of_ne_zero hp0).mp h1 with h | ⟨h, _⟩
  · exact h
  · exfalso
    have h2 := norm_nonneg ζ
    rw [h] at h2
    linarith

private lemma offLattice_zeta_pow'_MB (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) (hζ : IsPrimitiveRoot ζ p)
    (hp0 : p ≠ 0) {k : ℕ} (hk : ¬ p ∣ k) : OffLattice q (ζ ^ k) :=
  offLattice_of_norm_eq_one hq0 hq1
    (by rw [norm_pow, muT_norm_eq_one_of_isPrimitiveRoot_MB hζ hp0, one_pow])
    (fun h1 => hk ((hζ.pow_eq_one_iff_dvd k).mp h1))

theorem point_mul_eq_add_or_neg_of_symAddHyps_of_diff (hyps : SymAddHyps q)
    (hd1 : (pointX q (v * w) - pointX q (v * w⁻¹)) * (pointX q v - pointX q w) ^ 2 =
      -((2 * pointY q v + pointX q v) * (2 * pointY q w + pointX q w)))
    (hp : AddParams q v w) (hxne : pointX q v ≠ pointX q w)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (v * w)) (pointY q (v * w)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w)) :
    (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
        = Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃ ∨
      (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
        = -(Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃) := by
  have hd2 : (pointX q v - pointX q w) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hxne)

  have hS1 := hyps.sum v w hp
  rw [symSumNum_eq_b] at hS1
  have hsum := WeierstrassCurve.Affine.addX_add_addX_negY_mul_sq' (W := curve q)
    h₂.left h₃.left hxne
  have hsumEq : pointX q (v * w) + pointX q (v * w⁻¹) =
      (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w)) +
        (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v)
            ((curve q).toAffine.negY (pointX q w) (pointY q w))) :=
    mul_right_cancel₀ hd2 (hS1.trans hsum.symm)

  have hdiffC := WeierstrassCurve.Affine.addX_sub_addX_negY_mul_sq (W := curve q)
    (pointY q v) (pointY q w) hxne
  rw [sub_negY_curve, sub_negY_curve] at hdiffC
  have hdiffEq : pointX q (v * w) - pointX q (v * w⁻¹) =
      (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w)) -
        (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v)
            ((curve q).toAffine.negY (pointX q w) (pointY q w))) :=
    mul_right_cancel₀ hd2 (hd1.trans hdiffC.symm)

  have hxeq : pointX q (v * w) =
      (curve q).toAffine.addX (pointX q v) (pointX q w)
        ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w)) := by
    have h2 : (2 : K) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h2
    linear_combination hsumEq + hdiffEq

  have hcond : ¬(pointX q v = pointX q w ∧
      pointY q v = (curve q).toAffine.negY (pointX q w) (pointY q w)) :=
    fun hxy => hxne hxy.left
  have hns : (curve q).toAffine.Nonsingular
      ((curve q).toAffine.addX (pointX q v) (pointX q w)
        ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w)))
      ((curve q).toAffine.addY (pointX q v) (pointX q w) (pointY q v)
        ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w))) :=
    WeierstrassCurve.Affine.nonsingular_add h₂ h₃ hcond
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.left hns.left hxeq with hyeq | hyeq
  · left
    rw [Point.add_of_X_ne hxne]
    exact point_some_congr_MB hxeq hyeq h₁ _
  · right
    rw [Point.add_of_X_ne hxne, Point.neg_some]
    exact point_some_congr_MB hxeq hyeq h₁ _

theorem point_mul_eq_add_of_symAddHyps_of_diffHyp (hyps : SymAddHyps q) (hdiff : DiffHyp q)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hp : AddParams q v w) (hxne : pointX q v ≠ pointX q w)
    (hp' : AddParams q (v * w) v⁻¹) (hxne' : pointX q (v * w) ≠ pointX q v)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (v * w)) (pointY q (v * w)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w))
    (hP2 : (Point.some (pointX q v) (pointY q v) h₂ : (curve q).toAffine.Point)
        + Point.some (pointX q v) (pointY q v) h₂ ≠ 0) :
    (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃ := by

  have hvw0 : v * w ≠ 0 := mul_ne_zero hp.u_ne_zero hp.v_ne_zero
  have hprod0 : (v * w) * v⁻¹ ≠ 0 := mul_ne_zero hvw0 (inv_ne_zero hp.u_ne_zero)
  have h₄ : (curve q).toAffine.Nonsingular (pointX q ((v * w) * v⁻¹)) (pointY q ((v * w) * v⁻¹)) :=
    nonsingular_point hq0 hq hprod0 hp'.offLattice_mul
  have hinv0 : v⁻¹ ≠ 0 := inv_ne_zero hp.u_ne_zero
  have hinvOff : OffLattice q v⁻¹ := OffLattice.inv hq0 hp.offLattice_u
  have h₅ : (curve q).toAffine.Nonsingular (pointX q v⁻¹) (pointY q v⁻¹) :=
    nonsingular_point hq0 hq hinv0 hinvOff

  set R := (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
    with hR_def
  set P := (Point.some (pointX q v) (pointY q v) h₂ : (curve q).toAffine.Point) with hP_def
  set Q := (Point.some (pointX q w) (pointY q w) h₃ : (curve q).toAffine.Point) with hQ_def

  have hxneDer : pointX q (v * w) ≠ pointX q v⁻¹ := by
    rw [pointX_inv hq0 hp.u_ne_zero hp.offLattice_u]
    exact hxne'
  have hder := point_mul_eq_add_or_neg_of_symAddHyps_of_diff hyps
    (hdiff (v * w) v⁻¹ hp') hp' hxneDer h₄ h₁ h₅

  have helem : (v * w) * v⁻¹ = w := by
    rw [mul_comm v w, mul_assoc, mul_inv_cancel₀ hp.u_ne_zero, mul_one]
  have e₄ : (Point.some (pointX q ((v * w) * v⁻¹)) (pointY q ((v * w) * v⁻¹)) h₄ :
      (curve q).toAffine.Point) = Q :=
    point_some_congr_MB (congrArg (pointX q) helem) (congrArg (pointY q) helem) h₄ h₃
  have e₅ : (Point.some (pointX q v⁻¹) (pointY q v⁻¹) h₅ : (curve q).toAffine.Point) = -P :=
    point_inv_eq_neg hq0 hq hp.u_ne_zero hp.offLattice_u h₅ h₂
  rw [e₄, e₅] at hder

  rcases hder with hder | hder
  ·
    calc R = P + (R + -P) := by abel
      _ = P + Q := by rw [← hder]
  ·
    rcases point_mul_eq_add_or_neg_of_symAddHyps_of_diff hyps (hdiff v w hp) hp hxne h₁ h₂ h₃
      with hmain | hmain
    · exact hmain
    ·
      exfalso
      apply hP2
      have k1 : R + (P + Q) = 0 := by rw [hR_def, hmain]; abel
      have k2 : Q + (R + -P) = 0 := by rw [hder]; abel
      calc P + P = (R + (P + Q)) - (Q + (R + -P)) := by abel
        _ = 0 - 0 := by rw [k1, k2]
        _ = 0 := by abel

theorem zeta_pow_mul_self_point_eq_add (hyps : SymAddHyps q) (hdiff : DiffHyp q)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp5 : 5 ≤ p) (hpp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a * ζ ^ a)) (pointY q (ζ ^ a * ζ ^ a)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a)) (pointY q (ζ ^ a))) :
    (Point.some (pointX q (ζ ^ a * ζ ^ a)) (pointY q (ζ ^ a * ζ ^ a)) h₁ :
        (curve q).toAffine.Point)
      = Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂
          + Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂ := by

  have hp0 : p ≠ 0 := by omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp0
  have hζa0 : ζ ^ a ≠ 0 := pow_ne_zero _ hζ0
  have hq1 : ‖q‖ < 1 := by exact_mod_cast hq
  have hnζ : ‖ζ‖ = 1 := muT_norm_eq_one_of_isPrimitiveRoot_MB hζ hp0
  have hnζa : ‖ζ ^ a‖ = 1 := by rw [norm_pow, hnζ, one_pow]
  have hndvd_a : ¬ p ∣ a := fun hdvd =>
    absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have hndvd_2a : ¬ p ∣ a + a := by
    intro hdvd
    rw [← two_mul a] at hdvd
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h2 | ha
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact hndvd_a ha
  have hndvd_3a : ¬ p ∣ a + a + a := by
    intro hdvd
    have h3a : a + a + a = 3 * a := by ring
    rw [h3a] at hdvd
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h3 | ha
    · exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)
    · exact hndvd_a ha
  have hndvd_pa : ¬ p ∣ p - a := fun hdvd =>
    absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

  have hζaOff : OffLattice q (ζ ^ a) := offLattice_zeta_pow'_MB hq0 hq1 hζ hp0 hndvd_a
  have hζ2aOff : OffLattice q (ζ ^ a * ζ ^ a) := by
    rw [← pow_add]
    exact offLattice_zeta_pow'_MB hq0 hq1 hζ hp0 hndvd_2a
  have hζpaOff : OffLattice q (ζ ^ (p - a)) := offLattice_zeta_pow'_MB hq0 hq1 hζ hp0 hndvd_pa

  have hpa_inv : ζ ^ (p - a) = (ζ ^ a)⁻¹ := by
    have hcancel : ζ ^ a * ζ ^ (p - a) = ζ ^ a * (ζ ^ a)⁻¹ := by
      rw [mul_inv_cancel₀ hζa0, ← pow_add, show a + (p - a) = p by omega, hζ.pow_eq_one]
    exact mul_left_cancel₀ hζa0 hcancel

  have helem1 : (ζ ^ a * ζ ^ a) * ζ ^ (p - a) = ζ ^ a := by
    rw [mul_assoc, ← pow_add, show a + (p - a) = p by omega, hζ.pow_eq_one, mul_one]

  have hpDouble : AddParams q (ζ ^ a * ζ ^ a) (ζ ^ (p - a)) := by
    refine ⟨hq0, mul_ne_zero hζa0 hζa0, pow_ne_zero _ hζ0, hζ2aOff, hζpaOff, ?_, ?_⟩
    · rw [helem1]; exact hζaOff
    · have helem2 : (ζ ^ a * ζ ^ a) * (ζ ^ (p - a))⁻¹ = ζ ^ (a + a + a) := by
        rw [hpa_inv, inv_inv, ← pow_add, ← pow_add]
      rw [helem2]
      exact offLattice_zeta_pow'_MB hq0 hq1 hζ hp0 hndvd_3a

  have hxneDouble : pointX q (ζ ^ a * ζ ^ a) ≠ pointX q (ζ ^ (p - a)) := by
    intro hX
    rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq (mul_ne_zero hζa0 hζa0) (pow_ne_zero _ hζ0)
      hζ2aOff hζpaOff
      (le_of_eq (by rw [norm_mul, hnζa, one_mul]))
      (le_of_eq (by rw [norm_pow, hnζ, one_pow]))
      (by rw [helem1, hnζa]; exact hq1) hX with heq | hone
    ·
      apply hndvd_3a
      have h1 : ζ ^ (a + a + a) = 1 := by
        rw [pow_add, pow_add, heq, ← pow_add, show p - a + a = p by omega, hζ.pow_eq_one]
      exact (hζ.pow_eq_one_iff_dvd _).mp h1
    ·
      rw [helem1] at hone
      exact hndvd_a ((hζ.pow_eq_one_iff_dvd a).mp hone)

  have hprodNs : (curve q).toAffine.Nonsingular (pointX q ((ζ ^ a * ζ ^ a) * ζ ^ (p - a)))
      (pointY q ((ζ ^ a * ζ ^ a) * ζ ^ (p - a))) :=
    nonsingular_point hq0 hq (mul_ne_zero (mul_ne_zero hζa0 hζa0) (pow_ne_zero _ hζ0))
      hpDouble.offLattice_mul
  have hwNs : (curve q).toAffine.Nonsingular (pointX q (ζ ^ (p - a))) (pointY q (ζ ^ (p - a))) :=
    nonsingular_point hq0 hq (pow_ne_zero _ hζ0) hζpaOff

  have hcase := point_mul_eq_add_or_neg_of_symAddHyps_of_diff hyps
    (hdiff (ζ ^ a * ζ ^ a) (ζ ^ (p - a)) hpDouble) hpDouble hxneDouble hprodNs h₁ hwNs

  have e1 : (Point.some (pointX q ((ζ ^ a * ζ ^ a) * ζ ^ (p - a)))
      (pointY q ((ζ ^ a * ζ ^ a) * ζ ^ (p - a))) hprodNs : (curve q).toAffine.Point)
      = Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂ :=
    point_some_congr_MB (congrArg (pointX q) helem1) (congrArg (pointY q) helem1) hprodNs h₂
  have hwNs' : (curve q).toAffine.Nonsingular (pointX q ((ζ ^ a)⁻¹)) (pointY q ((ζ ^ a)⁻¹)) := by
    rw [← hpa_inv]
    exact hwNs
  have e2 : (Point.some (pointX q (ζ ^ (p - a))) (pointY q (ζ ^ (p - a))) hwNs :
      (curve q).toAffine.Point)
      = -(Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂) := by
    have e2' : (Point.some (pointX q (ζ ^ (p - a))) (pointY q (ζ ^ (p - a))) hwNs :
        (curve q).toAffine.Point)
        = Point.some (pointX q ((ζ ^ a)⁻¹)) (pointY q ((ζ ^ a)⁻¹)) hwNs' :=
      point_some_congr_MB (congrArg (pointX q) hpa_inv) (congrArg (pointY q) hpa_inv) hwNs hwNs'
    rw [e2']
    exact point_inv_eq_neg hq0 hq hζa0 hζaOff hwNs' h₂
  rw [e1, e2] at hcase

  set P2 := (Point.some (pointX q (ζ ^ a * ζ ^ a)) (pointY q (ζ ^ a * ζ ^ a)) h₁ :
    (curve q).toAffine.Point) with hP2_def
  set P1 := (Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂ :
    (curve q).toAffine.Point) with hP1_def
  rcases hcase with hc | hc
  ·
    calc P2 = (P2 + -P1) + P1 := by abel
      _ = P1 + P1 := by rw [← hc]
  ·
    exfalso
    have k : P1 + (P2 + -P1) = 0 := by
      nth_rewrite 1 [hc]
      abel
    have h0 : P2 = 0 := by
      calc P2 = P1 + (P2 + -P1) := by abel
        _ = 0 := k
    exact Point.some_ne_zero h₁ h0

private lemma muTranslation_aux_MB (hyps : SymAddHyps q) (hdiff : DiffHyp q)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp5 : 5 ≤ p) (hpp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p)
    {u : K} (hu0 : u ≠ 0) (hu : OffLattice q u) (hau : OffLattice q (ζ ^ a * u))
    (hule : ‖u‖ ≤ 1) (hqlt : ‖q‖ < ‖u‖)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a)) (pointY q (ζ ^ a)))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u)) :
    (Point.some (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂
          + Point.some (pointX q u) (pointY q u) h₃ := by

  have hp0 : p ≠ 0 := by omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp0
  have hζa0 : ζ ^ a ≠ 0 := pow_ne_zero _ hζ0
  have hq1 : ‖q‖ < 1 := by exact_mod_cast hq
  have hnζ : ‖ζ‖ = 1 := muT_norm_eq_one_of_isPrimitiveRoot_MB hζ hp0
  have hnζa : ‖ζ ^ a‖ = 1 := by rw [norm_pow, hnζ, one_pow]
  have hndvd_a : ¬ p ∣ a := fun hdvd =>
    absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have hndvd_2a : ¬ p ∣ a + a := by
    intro hdvd
    rw [← two_mul a] at hdvd
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h2 | ha
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact hndvd_a ha
  have hζaOff : OffLattice q (ζ ^ a) := offLattice_zeta_pow'_MB hq0 hq1 hζ hp0 hndvd_a
  have hζ2aOff : OffLattice q (ζ ^ a * ζ ^ a) := by
    rw [← pow_add]
    exact offLattice_zeta_pow'_MB hq0 hq1 hζ hp0 hndvd_2a

  have hDns : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a * ζ ^ a))
      (pointY q (ζ ^ a * ζ ^ a)) :=
    nonsingular_point hq0 hq (mul_ne_zero hζa0 hζa0) hζ2aOff

  by_cases hC2 : OffLattice q (ζ ^ a * u⁻¹)
  · by_cases hC4 : OffLattice q (ζ ^ a * ζ ^ a * u)
    ·
      have hpMain : AddParams q (ζ ^ a) u := ⟨hq0, hζa0, hu0, hζaOff, hu, hau, hC2⟩
      have hxneMain : pointX q (ζ ^ a) ≠ pointX q u := by
        intro hX
        rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hζa0 hu0 hζaOff hu (le_of_eq hnζa) hule
          (by rw [norm_mul, hnζa, one_mul]; exact hqlt) hX with heq | hone
        ·
          apply hC2 0
          rw [zpow_zero, one_mul, heq, mul_inv_cancel₀ hu0]
        ·
          exact hau 0 (by rw [zpow_zero, one_mul]; exact hone)
      have hpDer : AddParams q (ζ ^ a * u) (ζ ^ a)⁻¹ := by
        refine ⟨hq0, mul_ne_zero hζa0 hu0, inv_ne_zero hζa0, hau,
          OffLattice.inv hq0 hζaOff, ?_, ?_⟩
        · have helem : (ζ ^ a * u) * (ζ ^ a)⁻¹ = u := by
            rw [mul_comm (ζ ^ a) u, mul_assoc, mul_inv_cancel₀ hζa0, mul_one]
          rw [helem]; exact hu
        · have helem : (ζ ^ a * u) * ((ζ ^ a)⁻¹)⁻¹ = ζ ^ a * ζ ^ a * u := by
            rw [inv_inv]; ring
          rw [helem]; exact hC4
      have hxneDer : pointX q (ζ ^ a * u) ≠ pointX q (ζ ^ a) := by
        intro hX
        rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq (mul_ne_zero hζa0 hu0) hζa0 hau hζaOff
          (by rw [norm_mul, hnζa, one_mul]; exact hule) (le_of_eq hnζa)
          (by rw [norm_mul, norm_mul, hnζa, one_mul, mul_one]; exact hqlt) hX with heq | hone
        ·
          have hu1 : u = 1 := by
            have h := heq.trans (mul_one (ζ ^ a)).symm
            exact mul_left_cancel₀ hζa0 h
          exact hu 0 (by rw [zpow_zero, one_mul, hu1])
        ·
          apply hC4 0
          rw [zpow_zero, one_mul]
          calc ζ ^ a * ζ ^ a * u = (ζ ^ a * u) * ζ ^ a := by ring
            _ = 1 := hone

      have hP2 : (Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂ :
          (curve q).toAffine.Point)
          + Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂ ≠ 0 := by
        intro h2tor
        have hodd : Odd p := hpp.odd_of_ne_two (by omega)
        have hpow : (ζ ^ a) ^ p = q ^ (0 : ℤ) := by
          rw [← pow_mul, mul_comm a p, pow_mul, hζ.pow_eq_one, one_pow, zpow_zero]
        have hptor : p • (Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂ :
            (curve q).toAffine.Point) = 0 :=
          nsmul_prime_eq_zero hyps hq0 hq hζa0 hζaOff hpow hpp hodd h₂
        set PT := (Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂ :
          (curve q).toAffine.Point) with hPT_def
        obtain ⟨k, hk⟩ := hodd
        have hk' : p = k + k + 1 := by omega
        have hpP : p • PT = PT := by
          calc p • PT = (k + k + 1) • PT := by rw [← hk']
            _ = k • PT + k • PT + PT := by rw [add_nsmul, add_nsmul, one_nsmul]
            _ = k • (PT + PT) + PT := by rw [← nsmul_add]
            _ = PT := by rw [h2tor, smul_zero, zero_add]
        have h0 : PT = 0 := by rw [← hpP, hptor]
        exact Point.some_ne_zero h₂ h0
      exact point_mul_eq_add_of_symAddHyps_of_diffHyp hyps hdiff hq0 hq hpMain hxneMain hpDer
        hxneDer h₁ h₂ h₃ hP2
    ·
      have hdouble := zeta_pow_mul_self_point_eq_add hyps hdiff hq0 hq hp5 hpp hζ ha1 hap hDns h₂
      have hC4' : ∃ n : ℤ, q ^ n * (ζ ^ a * ζ ^ a * u) = 1 := by
        by_contra hcon
        exact hC4 (fun n hn => hcon ⟨n, hn⟩)
      obtain ⟨n, hn⟩ := hC4'

      have hqn0 : (q : K) ^ n ≠ 0 := zpow_ne_zero _ hq0
      have hzu_eq : ζ ^ a * u = q ^ (-n) * (ζ ^ a)⁻¹ := by
        have hcancel : (q ^ n * ζ ^ a) * (ζ ^ a * u) =
            (q ^ n * ζ ^ a) * (q ^ (-n) * (ζ ^ a)⁻¹) := by
          rw [show (q ^ n * ζ ^ a) * (ζ ^ a * u) = q ^ n * (ζ ^ a * ζ ^ a * u) by ring, hn,
            show (q ^ n * ζ ^ a) * (q ^ (-n) * (ζ ^ a)⁻¹) =
              (q ^ n * q ^ (-n)) * (ζ ^ a * (ζ ^ a)⁻¹) by ring,
            ← zpow_add₀ hq0, show n + -n = 0 by omega, zpow_zero,
            mul_inv_cancel₀ hζa0, mul_one]
        exact mul_left_cancel₀ (mul_ne_zero hqn0 hζa0) hcancel
      have hu_eq : u = q ^ (-n) * (ζ ^ a * ζ ^ a)⁻¹ := by
        have hcancel : (q ^ n * (ζ ^ a * ζ ^ a)) * u =
            (q ^ n * (ζ ^ a * ζ ^ a)) * (q ^ (-n) * (ζ ^ a * ζ ^ a)⁻¹) := by
          rw [show (q ^ n * (ζ ^ a * ζ ^ a)) * u = q ^ n * (ζ ^ a * ζ ^ a * u) by ring, hn,
            show (q ^ n * (ζ ^ a * ζ ^ a)) * (q ^ (-n) * (ζ ^ a * ζ ^ a)⁻¹) =
              (q ^ n * q ^ (-n)) * ((ζ ^ a * ζ ^ a) * (ζ ^ a * ζ ^ a)⁻¹) by ring,
            ← zpow_add₀ hq0, show n + -n = 0 by omega, zpow_zero,
            mul_inv_cancel₀ (mul_ne_zero hζa0 hζa0), mul_one]
        exact mul_left_cancel₀ (mul_ne_zero hqn0 (mul_ne_zero hζa0 hζa0)) hcancel

      have hXzu : pointX q (ζ ^ a * u) = pointX q (ζ ^ a) := by
        rw [hzu_eq, pointX_zpow_mul hq0, pointX_inv hq0 hζa0 hζaOff]
      have hYzu : pointY q (ζ ^ a * u) = -pointY q (ζ ^ a) - pointX q (ζ ^ a) := by
        rw [hzu_eq, pointY_zpow_mul hq0, pointY_inv hq0 hq hζa0 hζaOff]
      have hXu : pointX q u = pointX q (ζ ^ a * ζ ^ a) := by
        rw [hu_eq, pointX_zpow_mul hq0, pointX_inv hq0 (mul_ne_zero hζa0 hζa0) hζ2aOff]
      have hYu : pointY q u = -pointY q (ζ ^ a * ζ ^ a) - pointX q (ζ ^ a * ζ ^ a) := by
        rw [hu_eq, pointY_zpow_mul hq0, pointY_inv hq0 hq (mul_ne_zero hζa0 hζa0) hζ2aOff]

      have hL : (Point.some (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)) h₁ :
          (curve q).toAffine.Point)
          = -(Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂) := by
        rw [Point.neg_some]
        refine point_some_congr_MB hXzu ?_ h₁ _
        rw [hYzu, negY]
        show -pointY q (ζ ^ a) - pointX q (ζ ^ a) =
          -pointY q (ζ ^ a) - (curve q).a₁ * pointX q (ζ ^ a) - (curve q).a₃
        rw [curve_a₁, curve_a₃]
        ring
      have hU : (Point.some (pointX q u) (pointY q u) h₃ : (curve q).toAffine.Point)
          = -(Point.some (pointX q (ζ ^ a * ζ ^ a)) (pointY q (ζ ^ a * ζ ^ a)) hDns) := by
        rw [Point.neg_some]
        refine point_some_congr_MB hXu ?_ h₃ _
        rw [hYu, negY]
        show -pointY q (ζ ^ a * ζ ^ a) - pointX q (ζ ^ a * ζ ^ a) =
          -pointY q (ζ ^ a * ζ ^ a) - (curve q).a₁ * pointX q (ζ ^ a * ζ ^ a) - (curve q).a₃
        rw [curve_a₁, curve_a₃]
        ring
      rw [hL, hU, hdouble]
      abel
  ·

    have hdouble := zeta_pow_mul_self_point_eq_add hyps hdiff hq0 hq hp5 hpp hζ ha1 hap hDns h₂
    have hC2' : ∃ n : ℤ, q ^ n * (ζ ^ a * u⁻¹) = 1 := by
      by_contra hcon
      exact hC2 (fun n hn => hcon ⟨n, hn⟩)
    obtain ⟨n, hn⟩ := hC2'

    have hu_eq : u = q ^ n * ζ ^ a := by
      have h1 : (q ^ n * (ζ ^ a * u⁻¹)) * u = u := by rw [hn, one_mul]
      have h2 : (q ^ n * ζ ^ a) * (u⁻¹ * u) = u := by
        calc (q ^ n * ζ ^ a) * (u⁻¹ * u) = (q ^ n * (ζ ^ a * u⁻¹)) * u := by ring
          _ = u := h1
      rw [inv_mul_cancel₀ hu0, mul_one] at h2
      exact h2.symm

    have hXu : pointX q u = pointX q (ζ ^ a) := by rw [hu_eq, pointX_zpow_mul hq0]
    have hYu : pointY q u = pointY q (ζ ^ a) := by rw [hu_eq, pointY_zpow_mul hq0]
    have hzu_eq : ζ ^ a * u = q ^ n * (ζ ^ a * ζ ^ a) := by rw [hu_eq]; ring
    have hXzu : pointX q (ζ ^ a * u) = pointX q (ζ ^ a * ζ ^ a) := by
      rw [hzu_eq, pointX_zpow_mul hq0]
    have hYzu : pointY q (ζ ^ a * u) = pointY q (ζ ^ a * ζ ^ a) := by
      rw [hzu_eq, pointY_zpow_mul hq0]
    have hL : (Point.some (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)) h₁ :
        (curve q).toAffine.Point)
        = Point.some (pointX q (ζ ^ a * ζ ^ a)) (pointY q (ζ ^ a * ζ ^ a)) hDns :=
      point_some_congr_MB hXzu hYzu h₁ hDns
    have hU : (Point.some (pointX q u) (pointY q u) h₃ : (curve q).toAffine.Point)
        = Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂ :=
      point_some_congr_MB hXu hYu h₃ h₂
    rw [hL, hU]
    exact hdouble

theorem muTranslation_of_symAddHyps_of_diffHyp (hyps : SymAddHyps q) (hdiff : DiffHyp q)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp5 : 5 ≤ p) (hpp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) :
    MuTranslation q ζ p := by
  intro a ha1 hap u hu0 hu hau h₁ h₂ h₃

  have hq1 : ‖q‖ < 1 := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hupos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  obtain ⟨m, hm⟩ := exists_mem_Ioc_zpow (x := ‖u‖) (y := ‖q‖⁻¹) hupos
    ((one_lt_inv₀ hqpos).mpr hq1)
  have hinv_zpow : ∀ k : ℤ, (‖q‖⁻¹) ^ k = ‖q‖ ^ (-k) := by
    intro k
    rw [inv_zpow, ← zpow_neg]

  set u' := q ^ (m + 1) * u with hu'_def
  have hu'0 : u' ≠ 0 := mul_ne_zero (zpow_ne_zero _ hq0) hu0
  have hu' : OffLattice q u' := OffLattice.zpow_mul hq0 (m + 1) hu
  have hau' : OffLattice q (ζ ^ a * u') := by
    have helem : ζ ^ a * u' = q ^ (m + 1) * (ζ ^ a * u) := by rw [hu'_def]; ring
    rw [helem]
    exact OffLattice.zpow_mul hq0 (m + 1) hau

  have hnorm_u' : ‖u'‖ = ‖q‖ ^ (m + 1) * ‖u‖ := by
    rw [hu'_def, norm_mul, norm_zpow]
  have hu'le : ‖u'‖ ≤ 1 := by
    rw [hnorm_u']
    have h1 : ‖u‖ ≤ ‖q‖ ^ (-(m + 1)) := by
      have h2 := hm.2
      rwa [hinv_zpow (m + 1)] at h2
    calc ‖q‖ ^ (m + 1) * ‖u‖ ≤ ‖q‖ ^ (m + 1) * ‖q‖ ^ (-(m + 1)) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (zpow_pos hqpos _))
      _ = 1 := by
          rw [← zpow_add₀ (ne_of_gt hqpos), show m + 1 + -(m + 1) = 0 by omega, zpow_zero]
  have hu'gt : ‖q‖ < ‖u'‖ := by
    rw [hnorm_u']
    have h1 : ‖q‖ ^ (-m) < ‖u‖ := by
      have h2 := hm.1
      rwa [hinv_zpow m] at h2
    calc ‖q‖ = ‖q‖ ^ (m + 1) * ‖q‖ ^ (-m) := by
          rw [← zpow_add₀ (ne_of_gt hqpos), show m + 1 + -m = 1 by omega, zpow_one]
      _ < ‖q‖ ^ (m + 1) * ‖u‖ := mul_lt_mul_of_pos_left h1 (zpow_pos hqpos _)

  have hXu' : pointX q u' = pointX q u := by rw [hu'_def, pointX_zpow_mul hq0]
  have hYu' : pointY q u' = pointY q u := by rw [hu'_def, pointY_zpow_mul hq0]
  have hzuelem : ζ ^ a * u' = q ^ (m + 1) * (ζ ^ a * u) := by rw [hu'_def]; ring
  have hXzu' : pointX q (ζ ^ a * u') = pointX q (ζ ^ a * u) := by
    rw [hzuelem, pointX_zpow_mul hq0]
  have hYzu' : pointY q (ζ ^ a * u') = pointY q (ζ ^ a * u) := by
    rw [hzuelem, pointY_zpow_mul hq0]

  have h₁' : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a * u')) (pointY q (ζ ^ a * u')) := by
    rw [hXzu', hYzu']; exact h₁
  have h₃' : (curve q).toAffine.Nonsingular (pointX q u') (pointY q u') := by
    rw [hXu', hYu']; exact h₃

  have haux := muTranslation_aux_MB hyps hdiff hq0 hq hp5 hpp hζ ha1 hap hu'0 hu' hau'
    hu'le hu'gt h₁' h₂ h₃'
  have e₁ : (Point.some (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)) h₁ :
      (curve q).toAffine.Point)
      = Point.some (pointX q (ζ ^ a * u')) (pointY q (ζ ^ a * u')) h₁' :=
    point_some_congr_MB hXzu'.symm hYzu'.symm h₁ h₁'
  have e₃ : (Point.some (pointX q u) (pointY q u) h₃ : (curve q).toAffine.Point)
      = Point.some (pointX q u') (pointY q u') h₃' :=
    point_some_congr_MB hXu'.symm hYu'.symm h₃ h₃'
  rw [e₁, e₃]
  exact haux

end TateCurve

set_option linter.unusedSectionVars false

p2m_open "WeierstrassCurve.Affine P2MW.S_TateCurve_ks17_D2_exports.WeierstrassCurve.Affine"

namespace TateCurve
p2m_export "TateCurve" "eq_or_mul_eq_one_of_pointX_eq nsmul_prime_eq_zero SymAddHyps nonsingular_point SymAddHyps.sum symSumNum symSumNum_comm symSumNum_eq_b symProdNum_eq_b OffLattice OffLattice.zpow_mul OffLattice.q_mul OffLattice.inv AddParams addDefectSum offLattice_of_norm_eq_one xfun yfun pointX pointY b a₆ curve curve_a₁ curve_a₃ pointX_inv pointX_zpow_mul equation_pointX_pointY pointY_inv pointY_zpow_mul addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation ks17_A_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v w τ : K}

lemma offLattice_of_sq_norm_eq_zpow_odd (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (k : ℤ)
    (hw : ‖w‖ * ‖w‖ = ‖q‖ ^ (2 * k + 1)) : OffLattice q w := by
  intro n hn
  have ht0 : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have ht1 : ‖q‖ ≠ 1 := ne_of_lt hq
  have h1 : ‖(q : K) ^ n * w‖ = 1 := by rw [hn, norm_one]
  rw [norm_mul, norm_zpow] at h1
  have hcomb : ‖q‖ ^ (2 * k + 1) * (‖q‖ ^ n * ‖q‖ ^ n) = 1 := by
    calc ‖q‖ ^ (2 * k + 1) * (‖q‖ ^ n * ‖q‖ ^ n)
        = (‖w‖ * ‖w‖) * (‖q‖ ^ n * ‖q‖ ^ n) := by rw [hw]
      _ = (‖q‖ ^ n * ‖w‖) * (‖q‖ ^ n * ‖w‖) := by ring
      _ = 1 := by rw [h1]; ring
  rw [← zpow_add₀ (ne_of_gt ht0), ← zpow_add₀ (ne_of_gt ht0), ← zpow_zero ‖q‖] at hcomb
  have hinj := zpow_right_injective₀ ht0 ht1 hcomb
  omega

lemma not_onHalfLattice_of_sq_norm_eq_zpow_even (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (k : ℤ)
    (hw : ‖w‖ * ‖w‖ = ‖q‖ ^ (2 * k)) : ¬ OnHalfLattice q w := by
  rintro ⟨m, hm⟩
  have ht0 : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have ht1 : ‖q‖ ≠ 1 := ne_of_lt hq
  rw [norm_mul, norm_zpow] at hm
  have hm' : ‖q‖ ^ (2 * m + 2 * k) = ‖q‖ ^ (1 : ℤ) := by
    rw [zpow_add₀ (ne_of_gt ht0), zpow_one]
    calc ‖q‖ ^ (2 * m) * ‖q‖ ^ (2 * k)
        = (‖q‖ ^ m * ‖q‖ ^ m) * (‖w‖ * ‖w‖) := by
          rw [← hw, two_mul, zpow_add₀ (ne_of_gt ht0)]
      _ = (‖q‖ ^ m * ‖w‖) * (‖q‖ ^ m * ‖w‖) := by ring
      _ = ‖q‖ := hm
  have hinj := zpow_right_injective₀ ht0 ht1 hm'
  omega

private lemma sq_norm_mul_HL (a b : K) :
    ‖a * b‖ * ‖a * b‖ = (‖a‖ * ‖a‖) * (‖b‖ * ‖b‖) := by
  rw [norm_mul]; ring

private lemma sq_norm_inv_HL (a : K) : ‖a⁻¹‖ * ‖a⁻¹‖ = (‖a‖ * ‖a‖)⁻¹ := by
  rw [norm_inv]; rw [mul_inv]

lemma psiTwo_eq_zero_of_sq_eq_zpow (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hu0 : u ≠ 0)
    (hu : OffLattice q u) {k : ℤ} (hk : u ^ 2 = q ^ k) :
    2 * pointY q u + pointX q u = 0 := by
  have hq' : ‖q‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]; exact hq

  have hqk0 : (q : K) ^ k ≠ 0 := zpow_ne_zero k hq0
  have hinv : u⁻¹ = q ^ (-k) * u := by
    have h1 : u * u = q ^ k := by rw [← hk]; ring
    rw [zpow_neg, eq_comm, mul_comm, ← div_eq_mul_inv, div_eq_iff hqk0, ← h1,
      ← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  have hY := pointY_inv hq0 hq' hu0 hu
  rw [hinv, pointY_zpow_mul hq0] at hY
  linear_combination hY

lemma pointX_div_eq_mul_of_sq_eq_zpow (hq0 : q ≠ 0) (hp : AddParams q u v) {k : ℤ}
    (hk : u ^ 2 = q ^ k) : pointX q (u * v⁻¹) = pointX q (u * v) := by
  have hmul0 : u * v ≠ 0 := mul_ne_zero hp.u_ne_zero hp.v_ne_zero
  have hrw : u * v⁻¹ = q ^ k * (u * v)⁻¹ := by
    have h1 : u * u = q ^ k := by rw [← hk]; ring
    apply mul_right_cancel₀ hmul0
    calc u * v⁻¹ * (u * v) = u * u * (v⁻¹ * v) := by ring
      _ = q ^ k := by rw [h1, inv_mul_cancel₀ hp.v_ne_zero, mul_one]
      _ = q ^ k * ((u * v)⁻¹ * (u * v)) := by rw [inv_mul_cancel₀ hmul0, mul_one]
      _ = q ^ k * (u * v)⁻¹ * (u * v) := by ring
  rw [hrw, pointX_zpow_mul hq0, pointX_inv hq0 hmul0 hp.offLattice_mul]

private lemma point_some_congr'_HL {W : WeierstrassCurve K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

theorem point_mul_eq_add_or_neg_of_sum_of_diff
    (hS1 : (pointX q (v * w) + pointX q (v * w⁻¹)) * (pointX q v - pointX q w) ^ 2 =
      symSumNum q (pointX q v) (pointX q w))
    (hd1 : (pointX q (v * w) - pointX q (v * w⁻¹)) * (pointX q v - pointX q w) ^ 2 =
      -((2 * pointY q v + pointX q v) * (2 * pointY q w + pointX q w)))
    (_hp : AddParams q v w) (hxne : pointX q v ≠ pointX q w)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (v * w)) (pointY q (v * w)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w)) :
    (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
        = Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃ ∨
      (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
        = -(Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃) := by
  have hd2 : (pointX q v - pointX q w) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hxne)

  have hS1' := hS1
  rw [symSumNum_eq_b] at hS1'
  have hsum := WeierstrassCurve.Affine.addX_add_addX_negY_mul_sq' (W := curve q)
    h₂.left h₃.left hxne
  have hsumEq : pointX q (v * w) + pointX q (v * w⁻¹) =
      (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w)) +
        (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v)
            ((curve q).toAffine.negY (pointX q w) (pointY q w))) :=
    mul_right_cancel₀ hd2 (hS1'.trans hsum.symm)

  have hdiffC := WeierstrassCurve.Affine.addX_sub_addX_negY_mul_sq (W := curve q)
    (pointY q v) (pointY q w) hxne
  rw [sub_negY_curve, sub_negY_curve] at hdiffC
  have hdiffEq : pointX q (v * w) - pointX q (v * w⁻¹) =
      (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w)) -
        (curve q).toAffine.addX (pointX q v) (pointX q w)
          ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v)
            ((curve q).toAffine.negY (pointX q w) (pointY q w))) :=
    mul_right_cancel₀ hd2 (hd1.trans hdiffC.symm)

  have hxeq : pointX q (v * w) =
      (curve q).toAffine.addX (pointX q v) (pointX q w)
        ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w)) := by
    have h2 : (2 : K) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h2
    linear_combination hsumEq + hdiffEq

  have hcond : ¬(pointX q v = pointX q w ∧
      pointY q v = (curve q).toAffine.negY (pointX q w) (pointY q w)) :=
    fun hxy => hxne hxy.left
  have hns : (curve q).toAffine.Nonsingular
      ((curve q).toAffine.addX (pointX q v) (pointX q w)
        ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w)))
      ((curve q).toAffine.addY (pointX q v) (pointX q w) (pointY q v)
        ((curve q).toAffine.slope (pointX q v) (pointX q w) (pointY q v) (pointY q w))) :=
    WeierstrassCurve.Affine.nonsingular_add h₂ h₃ hcond
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.left hns.left hxeq with hyeq | hyeq
  · left
    rw [Point.add_of_X_ne hxne]
    exact point_some_congr'_HL hxeq hyeq h₁ _
  · right
    rw [Point.add_of_X_ne hxne, Point.neg_some]
    exact point_some_congr'_HL hxeq hyeq h₁ _

lemma pointX_ne_of_norm_ne (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {a b : K} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : OffLattice q a) (hb : OffLattice q b) (ha1 : ‖a‖ ≤ 1) (hb1 : ‖b‖ ≤ 1)
    (hab : ‖q‖ < ‖a * b‖) (hne : ‖a‖ ≠ ‖b‖) (hprod : ‖a * b‖ ≠ 1) :
    pointX q a ≠ pointX q b := by
  have hq' : ‖q‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]; exact hq
  intro hX
  rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq' ha0 hb0 ha hb ha1 hb1 hab hX with h | h
  · exact hne (by rw [h])
  · exact hprod (by rw [h, norm_one])

section TwoTorsionCase

theorem diff_identity_of_sq_eq_zpow (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hp : AddParams q u v) {k : ℤ} (hk : u ^ 2 = q ^ k) :
    (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) := by
  rw [pointX_div_eq_mul_of_sq_eq_zpow hq0 hp hk,
    psiTwo_eq_zero_of_sq_eq_zpow hq0 hq hp.u_ne_zero hp.offLattice_u hk]
  ring

theorem symAdd_sum_of_offLocus_of_sq_eq_zpow (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hS1 : ∀ a b : K, AddParams q a b → ¬(OnHalfLattice q a ∧ OnHalfLattice q b) →
      (pointX q (a * b) + pointX q (a * b⁻¹)) * (pointX q a - pointX q b) ^ 2 =
        symSumNum q (pointX q a) (pointX q b))
    (hD1 : ∀ a b : K, AddParams q a b → ¬(OnHalfLattice q a ∧ OnHalfLattice q b) →
      (pointX q (a * b) - pointX q (a * b⁻¹)) * (pointX q a - pointX q b) ^ 2 =
        -((2 * pointY q a + pointX q a) * (2 * pointY q b + pointX q b)))
    (hp : AddParams q u v) (hu2 : ‖u‖ * ‖u‖ = ‖q‖) (hv2 : ‖v‖ * ‖v‖ = ‖q‖)
    {k : ℤ} (hk : u ^ 2 = q ^ k) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) := by
  have hq' : ‖q‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]; exact hq
  have ht0 : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hψu : 2 * pointY q u + pointX q u = 0 :=
    psiTwo_eq_zero_of_sq_eq_zpow hq0 hq hp.u_ne_zero hp.offLattice_u hk
  have hXcollapse : pointX q (u * v⁻¹) = pointX q (u * v) :=
    pointX_div_eq_mul_of_sq_eq_zpow hq0 hp hk

  by_cases hxuv : pointX q u = pointX q v
  · have heq := equation_pointX_pointY hq0 hq' hp.u_ne_zero hp.offLattice_u
    rw [← hxuv]
    unfold symSumNum
    linear_combination 4 * heq + (-(2 * pointY q u + pointX q u)) * hψu

  ·
    have hmul0 : u * v ≠ 0 := mul_ne_zero hp.u_ne_zero hp.v_ne_zero
    have hcancel : u * v * u⁻¹ = v := by
      rw [mul_comm u v, mul_assoc, mul_inv_cancel₀ hp.u_ne_zero, mul_one]
    have hPaux : AddParams q (u * v) u⁻¹ :=
      { q_ne_zero := hq0
        u_ne_zero := hmul0
        v_ne_zero := inv_ne_zero hp.u_ne_zero
        offLattice_u := hp.offLattice_mul
        offLattice_v := OffLattice.inv hq0 hp.offLattice_u
        offLattice_mul := by
          rw [hcancel]; exact hp.offLattice_v
        offLattice_div := by
          have h1 : u * v * u⁻¹⁻¹ = q ^ k * v := by
            rw [inv_inv]
            calc u * v * u = u ^ 2 * v := by ring
              _ = q ^ k * v := by rw [hk]
          rw [h1]
          exact OffLattice.zpow_mul hq0 k hp.offLattice_v }
    have hnotloc : ¬ (OnHalfLattice q (u * v) ∧ OnHalfLattice q u⁻¹) := by
      intro hcon
      exact (not_onHalfLattice_of_sq_norm_eq_zpow_even hq0 hq 1
        (by rw [sq_norm_mul_HL, hu2, hv2]; rw [show (2 : ℤ) * 1 = 1 + 1 by norm_num,
          zpow_add₀ (ne_of_gt ht0), zpow_one])) hcon.1

    have hS1aux := hS1 (u * v) u⁻¹ hPaux hnotloc

    have he2 : u * v * u⁻¹⁻¹ = q ^ k * v := by
      rw [inv_inv]
      calc u * v * u = u ^ 2 * v := by ring
        _ = q ^ k * v := by rw [hk]
    rw [hcancel, he2, pointX_zpow_mul hq0,
      pointX_inv hq0 hp.u_ne_zero hp.offLattice_u] at hS1aux

    have hnsU : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u) :=
      nonsingular_point hq0 hq' hp.u_ne_zero hp.offLattice_u
    have hnsUV : (curve q).toAffine.Nonsingular (pointX q (u * v)) (pointY q (u * v)) :=
      nonsingular_point hq0 hq' hmul0 hp.offLattice_mul
    have hnsV : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v) :=
      nonsingular_point hq0 hq' hp.v_ne_zero hp.offLattice_v

    have hnormuv : ‖u * v‖ = ‖q‖ := by
      have h1 : ‖u * v‖ * ‖u * v‖ = ‖q‖ * ‖q‖ := by rw [sq_norm_mul_HL, hu2, hv2]
      rcases mul_self_eq_mul_self_iff.mp h1 with h | h
      · exact h
      · have := norm_nonneg (u * v)
        linarith
    have hnormu_le : ‖u‖ ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have h1 : 1 * 1 < ‖u‖ * ‖u‖ := by
        apply mul_lt_mul'' hgt hgt <;> norm_num
      rw [hu2, one_mul] at h1
      linarith [hq]
    have hnormu_gt : ‖q‖ < ‖u‖ := by
      by_contra hle
      push Not at hle
      have h1 : ‖u‖ * ‖u‖ ≤ ‖q‖ * ‖q‖ :=
        mul_le_mul hle hle (norm_nonneg u) ht0.le
      rw [hu2] at h1
      nlinarith [ht0, hq]
    have hXuvu : pointX q (u * v) ≠ pointX q u := by
      intro hX
      set b := q * (u * v)⁻¹ with hb_def
      have hb0 : b ≠ 0 := mul_ne_zero hq0 (inv_ne_zero hmul0)
      have hbOff : OffLattice q b :=
        OffLattice.q_mul hq0 (OffLattice.inv hq0 hp.offLattice_mul)
      have hbnorm : ‖b‖ = 1 := by
        rw [hb_def, norm_mul, norm_inv, hnormuv]
        exact mul_inv_cancel₀ (ne_of_gt ht0)
      have hXb : pointX q b = pointX q (u * v) := by
        rw [hb_def, show q * (u * v)⁻¹ = q ^ (1 : ℤ) * (u * v)⁻¹ by rw [zpow_one],
          pointX_zpow_mul hq0, pointX_inv hq0 hmul0 hp.offLattice_mul]
      have hX' : pointX q u = pointX q b := by rw [hXb, hX]
      have hband : ‖q‖ < ‖u * b‖ := by
        rw [norm_mul, hbnorm, mul_one]
        exact hnormu_gt
      rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq' hp.u_ne_zero hb0 hp.offLattice_u
        hbOff hnormu_le (le_of_eq hbnorm) hband hX' with h | h
      ·
        apply hp.offLattice_v (k - 1)
        have h2 : u * (u * v) = q := by
          nth_rewrite 1 [h]
          rw [hb_def, mul_assoc, inv_mul_cancel₀ hmul0, mul_one]
        have h3 : q ^ k * v = q := by
          calc q ^ k * v = u ^ 2 * v := by rw [hk]
            _ = u * (u * v) := by ring
            _ = q := h2
        calc q ^ (k - 1) * v = q ^ (-1 : ℤ) * (q ^ k * v) := by
              rw [← mul_assoc, ← zpow_add₀ hq0]
              congr 1
              ring
          _ = q ^ (-1 : ℤ) * q := by rw [h3]
          _ = 1 := by rw [zpow_neg, zpow_one]; exact inv_mul_cancel₀ hq0
      ·
        apply hp.offLattice_v (-1)
        have h2 : u * q = u * v := by
          have h3 : u * b * (u * v) = u * v := by rw [h, one_mul]
          rw [hb_def] at h3
          have h4 : u * q * ((u * v)⁻¹ * (u * v)) = u * v := by
            calc u * q * ((u * v)⁻¹ * (u * v)) = u * (q * (u * v)⁻¹) * (u * v) := by ring
              _ = u * v := h3
          rwa [inv_mul_cancel₀ hmul0, mul_one] at h4
        have h5 : q = v := mul_left_cancel₀ hp.u_ne_zero h2
        rw [← h5, zpow_neg, zpow_one]
        exact inv_mul_cancel₀ hq0

    have hsum := WeierstrassCurve.Affine.addX_add_addX_negY_mul_sq' (W := curve q)
      hnsUV.left hnsU.left hXuvu
    rw [← symSumNum_eq_b] at hsum

    have hnegYu : (curve q).toAffine.negY (pointX q u) (pointY q u) = pointY q u := by
      show -pointY q u - (curve q).a₁ * pointX q u - (curve q).a₃ = pointY q u
      rw [curve_a₁, curve_a₃]
      linear_combination -hψu
    rw [hnegYu] at hsum

    have hd2 : (pointX q (u * v) - pointX q u) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.mpr hXuvu)
    have haddX : (curve q).toAffine.addX (pointX q (u * v)) (pointX q u)
        ((curve q).toAffine.slope (pointX q (u * v)) (pointX q u)
          (pointY q (u * v)) (pointY q u)) = pointX q v := by
      have h2 : (2 : K) ≠ 0 := by norm_num
      apply mul_left_cancel₀ h2
      apply mul_right_cancel₀ hd2
      calc 2 * ((curve q).toAffine.addX (pointX q (u * v)) (pointX q u)
            ((curve q).toAffine.slope (pointX q (u * v)) (pointX q u)
              (pointY q (u * v)) (pointY q u))) * (pointX q (u * v) - pointX q u) ^ 2
          = ((curve q).toAffine.addX (pointX q (u * v)) (pointX q u)
              ((curve q).toAffine.slope (pointX q (u * v)) (pointX q u)
                (pointY q (u * v)) (pointY q u)) +
             (curve q).toAffine.addX (pointX q (u * v)) (pointX q u)
              ((curve q).toAffine.slope (pointX q (u * v)) (pointX q u)
                (pointY q (u * v)) (pointY q u))) * (pointX q (u * v) - pointX q u) ^ 2 := by
            ring
        _ = symSumNum q (pointX q (u * v)) (pointX q u) := hsum
        _ = (pointX q v + pointX q v) * (pointX q (u * v) - pointX q u) ^ 2 := by
            linear_combination -hS1aux
        _ = 2 * pointX q v * (pointX q (u * v) - pointX q u) ^ 2 := by ring

    have hsumGoal := WeierstrassCurve.Affine.addX_add_addX_negY_mul_sq' (W := curve q)
      hnsU.left hnsV.left hxuv
    rw [← symSumNum_eq_b] at hsumGoal

    have hdiffC := WeierstrassCurve.Affine.addX_sub_addX_negY_mul_sq (W := curve q)
      (pointY q u) (pointY q v) hxuv
    rw [sub_negY_curve, sub_negY_curve, hψu] at hdiffC
    have hAeqB : (curve q).toAffine.addX (pointX q u) (pointX q v)
        ((curve q).toAffine.slope (pointX q u) (pointX q v) (pointY q u) (pointY q v)) =
        (curve q).toAffine.addX (pointX q u) (pointX q v)
          ((curve q).toAffine.slope (pointX q u) (pointX q v) (pointY q u)
            ((curve q).toAffine.negY (pointX q v) (pointY q v))) := by
      have hd2' : (pointX q u - pointX q v) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (sub_ne_zero.mpr hxuv)
      have h0 : ((curve q).toAffine.addX (pointX q u) (pointX q v)
          ((curve q).toAffine.slope (pointX q u) (pointX q v) (pointY q u) (pointY q v)) -
            (curve q).toAffine.addX (pointX q u) (pointX q v)
              ((curve q).toAffine.slope (pointX q u) (pointX q v) (pointY q u)
                ((curve q).toAffine.negY (pointX q v) (pointY q v)))) *
          (pointX q u - pointX q v) ^ 2 = 0 := by
        rw [hdiffC]; ring
      have h1 := (mul_eq_zero.mp h0).resolve_right hd2'
      exact sub_eq_zero.mp h1

    have hnsUinv : (curve q).toAffine.Nonsingular (pointX q u⁻¹) (pointY q u⁻¹) :=
      nonsingular_point hq0 hq' (inv_ne_zero hp.u_ne_zero) (OffLattice.inv hq0 hp.offLattice_u)
    have hXuvuinv : pointX q (u * v) ≠ pointX q u⁻¹ := by
      rw [pointX_inv hq0 hp.u_ne_zero hp.offLattice_u]; exact hXuvu
    have hD1aux := hD1 (u * v) u⁻¹ hPaux hnotloc
    have hdich := point_mul_eq_add_or_neg_of_sum_of_diff (hS1 (u * v) u⁻¹ hPaux hnotloc)
      hD1aux hPaux hXuvuinv
      (nonsingular_point hq0 hq' (mul_ne_zero hmul0 (inv_ne_zero hp.u_ne_zero))
        hPaux.offLattice_mul)
      hnsUV hnsUinv

    have e₄ : (Point.some (pointX q (u * v * u⁻¹)) (pointY q (u * v * u⁻¹))
        (nonsingular_point hq0 hq' (mul_ne_zero hmul0 (inv_ne_zero hp.u_ne_zero))
          hPaux.offLattice_mul) : (curve q).toAffine.Point) =
        Point.some (pointX q v) (pointY q v) hnsV :=
      point_some_congr'_HL (by rw [hcancel]) (by rw [hcancel]) _ _
    have e₅ : (Point.some (pointX q u⁻¹) (pointY q u⁻¹) hnsUinv : (curve q).toAffine.Point) =
        -Point.some (pointX q u) (pointY q u) hnsU :=
      point_inv_eq_neg hq0 hq' hp.u_ne_zero hp.offLattice_u hnsUinv hnsU
    rw [e₄, e₅] at hdich

    have hxinvne : pointX q u ≠ pointX q v := hxuv
    rcases hdich with hcase | hcase
    ·
      have hpt : (Point.some (pointX q (u * v)) (pointY q (u * v)) hnsUV :
          (curve q).toAffine.Point) =
          Point.some (pointX q u) (pointY q u) hnsU +
            Point.some (pointX q v) (pointY q v) hnsV := by
        rw [hcase]; abel
      rw [Point.add_of_X_ne hxinvne] at hpt
      simp only [Point.some.injEq] at hpt
      rw [hXcollapse, hpt.1]
      linear_combination hsumGoal + ((pointX q u - pointX q v) ^ 2) * hAeqB
    ·
      have hpt : (Point.some (pointX q (u * v)) (pointY q (u * v)) hnsUV :
          (curve q).toAffine.Point) =
          Point.some (pointX q u) (pointY q u) hnsU +
            -Point.some (pointX q v) (pointY q v) hnsV := by
        rw [hcase]; abel
      rw [Point.neg_some, Point.add_of_X_ne hxinvne] at hpt
      simp only [Point.some.injEq] at hpt
      rw [hXcollapse, hpt.1]
      linear_combination hsumGoal - ((pointX q u - pointX q v) ^ 2) * hAeqB

end TwoTorsionCase

variable (q τ) in

def GenericHalfLatticeAddition : Prop :=
  ∀ u v : K, AddParams q u v → ‖u‖ * ‖u‖ = ‖q‖ → ‖v‖ * ‖v‖ = ‖q‖ →
    OffLattice q (u * τ⁻¹) → OffLattice q (v * τ⁻¹) →
    ((pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        symSumNum q (pointX q u) (pointX q v)) ∧
      ((pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)))

lemma sq_eq_zpow_of_not_offLattice_shift (hq0 : q ≠ 0) (hτ : τ ^ 2 = q)
    (h : ¬ OffLattice q (u * τ⁻¹)) : ∃ k : ℤ, u ^ 2 = q ^ k := by
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0] at hτ
    exact hq0 (by simpa using hτ.symm)
  obtain ⟨n, hn⟩ := not_forall.mp h
  rw [not_ne_iff] at hn
  refine ⟨1 - 2 * n, ?_⟩
  have h2 : u * τ⁻¹ = q ^ (-n) := by
    have h3 := congrArg (fun x => q ^ (-n) * x) hn
    rwa [← mul_assoc, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, one_mul, mul_one] at h3
  have h1 : u = q ^ (-n) * τ := by
    have h4 := congrArg (fun x => x * τ) h2
    rwa [mul_assoc, inv_mul_cancel₀ hτ0, mul_one] at h4
  rw [h1]
  have hexp : ((q : K) ^ (-n) * τ) ^ 2 = q ^ (-n) * q ^ (-n) * τ ^ 2 := by ring
  rw [hexp, hτ]
  calc q ^ (-n) * q ^ (-n) * q = q ^ (-n) * q ^ (-n) * q ^ (1 : ℤ) := by rw [zpow_one]
    _ = q ^ (-n + -n + 1) := by rw [← zpow_add₀ hq0, ← zpow_add₀ hq0]
    _ = q ^ (1 - 2 * n) := by congr 1; ring

private lemma shift_values_HL (hq0 : q ≠ 0) (m n : ℤ) :
    pointX q (q ^ m * u) = pointX q u ∧ pointY q (q ^ m * u) = pointY q u ∧
      pointX q ((q ^ m * u) * (q ^ n * v)) = pointX q (u * v) ∧
      pointX q ((q ^ m * u) * (q ^ n * v)⁻¹) = pointX q (u * v⁻¹) := by
  refine ⟨pointX_zpow_mul hq0 m, pointY_zpow_mul hq0 m, ?_, ?_⟩
  · have h1 : (q ^ m * u) * (q ^ n * v) = q ^ (m + n) * (u * v) := by
      rw [zpow_add₀ hq0]; ring
    rw [h1, pointX_zpow_mul hq0]
  · have h1 : (q ^ m * u) * (q ^ n * v)⁻¹ = q ^ (m - n) * (u * v⁻¹) := by
      rw [mul_inv, ← zpow_neg, show m - n = m + -n from by ring, zpow_add₀ hq0]
      ring
    rw [h1, pointX_zpow_mul hq0]

theorem symAdd_sum_of_offLocus_families (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hgen : GenericHalfLatticeAddition q τ)
    (hS1 : ∀ a b : K, AddParams q a b → ¬(OnHalfLattice q a ∧ OnHalfLattice q b) →
      (pointX q (a * b) + pointX q (a * b⁻¹)) * (pointX q a - pointX q b) ^ 2 =
        symSumNum q (pointX q a) (pointX q b))
    (hD1 : ∀ a b : K, AddParams q a b → ¬(OnHalfLattice q a ∧ OnHalfLattice q b) →
      (pointX q (a * b) - pointX q (a * b⁻¹)) * (pointX q a - pointX q b) ^ 2 =
        -((2 * pointY q a + pointX q a) * (2 * pointY q b + pointX q b)))
    (hp : AddParams q u v) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) := by
  by_cases hloc : OnHalfLattice q u ∧ OnHalfLattice q v
  ·
    obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := hloc
    set u₀ := q ^ m * u with hu₀
    set v₀ := q ^ n * v with hv₀
    have hp₀ : AddParams q u₀ v₀ := hp.latticeRep ⟨m, Or.inl hu₀⟩ ⟨n, Or.inl hv₀⟩
    obtain ⟨hXu, hYu, hXmul, hXdiv⟩ := shift_values_HL (u := u) (v := v) hq0 m n

    suffices h : (pointX q (u₀ * v₀) + pointX q (u₀ * v₀⁻¹)) *
        (pointX q u₀ - pointX q v₀) ^ 2 = symSumNum q (pointX q u₀) (pointX q v₀) by
      obtain ⟨hXv, hYv, _, _⟩ := shift_values_HL (u := v) (v := u) hq0 n m
      rw [hu₀, hv₀, hXu, hXv, hXmul, hXdiv] at h
      exact h

    have hu2 : ‖u₀‖ * ‖u₀‖ = ‖q‖ := hm
    have hv2 : ‖v₀‖ * ‖v₀‖ = ‖q‖ := hn
    by_cases hu' : OffLattice q (u₀ * τ⁻¹)
    · by_cases hv' : OffLattice q (v₀ * τ⁻¹)
      · exact (hgen u₀ v₀ hp₀ hu2 hv2 hu' hv').1
      ·
        obtain ⟨k, hk⟩ := sq_eq_zpow_of_not_offLattice_shift hq0 hτ hv'
        have h := symAdd_sum_of_offLocus_of_sq_eq_zpow hq0 hq hS1 hD1 hp₀.swap hv2 hu2 hk
        have hswapmul : pointX q (v₀ * u₀) = pointX q (u₀ * v₀) := by rw [mul_comm]
        have hswapdiv : pointX q (v₀ * u₀⁻¹) = pointX q (u₀ * v₀⁻¹) := by
          have h1 : v₀ * u₀⁻¹ = (u₀ * v₀⁻¹)⁻¹ := by
            rw [eq_comm, mul_inv_rev, inv_inv]
          rw [h1, pointX_inv hq0 (mul_ne_zero hp₀.u_ne_zero (inv_ne_zero hp₀.v_ne_zero))
            hp₀.offLattice_div]
        rw [hswapmul, hswapdiv, symSumNum_comm] at h
        linear_combination h
    ·
      obtain ⟨k, hk⟩ := sq_eq_zpow_of_not_offLattice_shift hq0 hτ hu'
      exact symAdd_sum_of_offLocus_of_sq_eq_zpow hq0 hq hS1 hD1 hp₀ hu2 hv2 hk
  · exact hS1 u v hp hloc

theorem diff_identity_of_offLocus_families (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hgen : GenericHalfLatticeAddition q τ)
    (_hS1 : ∀ a b : K, AddParams q a b → ¬(OnHalfLattice q a ∧ OnHalfLattice q b) →
      (pointX q (a * b) + pointX q (a * b⁻¹)) * (pointX q a - pointX q b) ^ 2 =
        symSumNum q (pointX q a) (pointX q b))
    (hD1 : ∀ a b : K, AddParams q a b → ¬(OnHalfLattice q a ∧ OnHalfLattice q b) →
      (pointX q (a * b) - pointX q (a * b⁻¹)) * (pointX q a - pointX q b) ^ 2 =
        -((2 * pointY q a + pointX q a) * (2 * pointY q b + pointX q b)))
    (hp : AddParams q u v) :
    (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) := by
  by_cases hloc : OnHalfLattice q u ∧ OnHalfLattice q v
  · obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := hloc
    set u₀ := q ^ m * u with hu₀
    set v₀ := q ^ n * v with hv₀
    have hp₀ : AddParams q u₀ v₀ := hp.latticeRep ⟨m, Or.inl hu₀⟩ ⟨n, Or.inl hv₀⟩
    obtain ⟨hXu, hYu, hXmul, hXdiv⟩ := shift_values_HL (u := u) (v := v) hq0 m n
    obtain ⟨hXv, hYv, _, _⟩ := shift_values_HL (u := v) (v := u) hq0 n m
    suffices h : (pointX q (u₀ * v₀) - pointX q (u₀ * v₀⁻¹)) *
        (pointX q u₀ - pointX q v₀) ^ 2 =
        -((2 * pointY q u₀ + pointX q u₀) * (2 * pointY q v₀ + pointX q v₀)) by
      rw [hu₀, hv₀, hXu, hXv, hYu, hYv, hXmul, hXdiv] at h
      exact h
    have hu2 : ‖u₀‖ * ‖u₀‖ = ‖q‖ := hm
    have hv2 : ‖v₀‖ * ‖v₀‖ = ‖q‖ := hn
    by_cases hu' : OffLattice q (u₀ * τ⁻¹)
    · by_cases hv' : OffLattice q (v₀ * τ⁻¹)
      · exact (hgen u₀ v₀ hp₀ hu2 hv2 hu' hv').2
      ·
        obtain ⟨k, hk⟩ := sq_eq_zpow_of_not_offLattice_shift hq0 hτ hv'
        have h := diff_identity_of_sq_eq_zpow hq0 hq hp₀.swap hk
        have hswapmul : pointX q (v₀ * u₀) = pointX q (u₀ * v₀) := by rw [mul_comm]
        have hswapdiv : pointX q (v₀ * u₀⁻¹) = pointX q (u₀ * v₀⁻¹) := by
          have h1 : v₀ * u₀⁻¹ = (u₀ * v₀⁻¹)⁻¹ := by
            rw [eq_comm, mul_inv_rev, inv_inv]
          rw [h1, pointX_inv hq0 (mul_ne_zero hp₀.u_ne_zero (inv_ne_zero hp₀.v_ne_zero))
            hp₀.offLattice_div]
        rw [hswapmul, hswapdiv] at h
        linear_combination h
    · obtain ⟨k, hk⟩ := sq_eq_zpow_of_not_offLattice_shift hq0 hτ hu'
      exact diff_identity_of_sq_eq_zpow hq0 hq hp₀ hk
  · exact hD1 u v hp hloc

theorem symAdd_sum_of_region_all (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hgen : GenericHalfLatticeAddition q τ)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) :=
  symAdd_sum_of_offLocus_families hq0 hq hτ hgen
    (fun _ _ hab hnl => symAdd_sum_of_region_of_not_halfLattice hq0 hq hregS1 hab hnl)
    (fun _ _ hab hnl => diff_identity_of_region_of_not_halfLattice hq0 hq hregD1 hab hnl) hp

theorem diff_identity_of_region_all (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hgen : GenericHalfLatticeAddition q τ)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v) :
    (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) :=
  diff_identity_of_offLocus_families hq0 hq hτ hgen
    (fun _ _ hab hnl => symAdd_sum_of_region_of_not_halfLattice hq0 hq hregS1 hab hnl)
    (fun _ _ hab hnl => diff_identity_of_region_of_not_halfLattice hq0 hq hregD1 hab hnl) hp

theorem diffHyp_of_region (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hgen : GenericHalfLatticeAddition q τ)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v'))) :
    DiffHyp q :=
  fun _ _ hp => diff_identity_of_region_all hq0 hq hτ hgen hregS1 hregD1 hp

lemma exists_sqrt_of_isAlgClosed [IsAlgClosed K] (q : K) : ∃ τ : K, τ ^ 2 = q :=
  IsAlgClosed.exists_pow_nat_eq q (n := 2) (by norm_num)

end TateCurve

set_option linter.unusedSectionVars false

p2m_open "WeierstrassCurve.Affine P2MW.S_TateCurve_ks17_D2_exports.WeierstrassCurve.Affine"

namespace TateCurve
p2m_export "TateCurve" "eq_or_mul_eq_one_of_pointX_eq nsmul_prime_eq_zero SymAddHyps nonsingular_point SymAddHyps.sum symSumNum symSumNum_comm symSumNum_eq_b symProdNum_eq_b OffLattice OffLattice.zpow_mul OffLattice.q_mul OffLattice.inv AddParams addDefectSum offLattice_of_norm_eq_one xfun yfun pointX pointY b a₆ curve curve_a₁ curve_a₃ pointX_inv pointX_zpow_mul equation_pointX_pointY pointY_inv pointY_zpow_mul addDefectDiff DiffHyp ExpansionRegion addDefectSumCoeff psiCoeffFull addDefectDiffCoeff LatticeRep OnHalfLattice MuTranslation ks17_A_exports"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v τ : K}

private lemma point_some_congr_HL2 {W : WeierstrassCurve K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

private lemma addX_eq_of_add_eq_or_neg_HL2 {W : WeierstrassCurve K} {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : K}
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂}
    {h₃ : W.toAffine.Nonsingular x₃ y₃} {h₄ : W.toAffine.Nonsingular x₄ y₄}
    (hx12 : x₁ ≠ x₂) (hx34 : x₃ ≠ x₄)
    (heq : (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : W.toAffine.Point) =
        Point.some x₃ y₃ h₃ + Point.some x₄ y₄ h₄ ∨
      (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : W.toAffine.Point) =
        -(Point.some x₃ y₃ h₃ + Point.some x₄ y₄ h₄)) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) =
      W.toAffine.addX x₃ x₄ (W.toAffine.slope x₃ x₄ y₃ y₄) := by
  rcases heq with heq | heq
  · rw [Point.add_of_X_ne hx12, Point.add_of_X_ne hx34] at heq
    simp only [Point.some.injEq] at heq
    exact heq.1
  · rw [Point.add_of_X_ne hx12, Point.add_of_X_ne hx34, Point.neg_some] at heq
    simp only [Point.some.injEq] at heq
    exact heq.1

private lemma psiTwo_eq_zero_of_double_eq_zero_HL2 {x y : K}
    (h : (curve q).toAffine.Nonsingular x y)
    (hd : (Point.some x y h : (curve q).toAffine.Point) + Point.some x y h = 0) :
    2 * y + x = 0 := by
  have hneg : (Point.some x y h : (curve q).toAffine.Point) = -Point.some x y h :=
    add_eq_zero_iff_eq_neg.mp hd
  rw [Point.neg_some] at hneg
  simp only [Point.some.injEq] at hneg
  have h2 := hneg.2
  simp only [negY, curve_a₁, curve_a₃] at h2
  linear_combination h2

private lemma eq_or_eq_neg_trans_HL2 {G : Type*} [AddCommGroup G] {a b p w : G}
    (h1 : p = a ∨ p = -a) (h2 : w = b ∨ w = -b) (h3 : p = w ∨ p = -w) :
    a = b ∨ a = -b := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
  · rw [h1, h2] at h3; exact Or.inl h3
  · rw [h1, h2] at h3; exact Or.inr h3
  · rw [h1, h2] at h3; exact Or.inr h3
  · rw [h1, h2, neg_neg] at h3; exact Or.inl h3
  · rw [h1, h2] at h3; exact Or.inr (neg_eq_iff_eq_neg.mp h3)
  · rw [h1, h2] at h3; exact Or.inl (neg_inj.mp h3)
  · rw [h1, h2] at h3; exact Or.inl (neg_inj.mp h3)
  · rw [h1, h2, neg_neg] at h3; exact Or.inr (neg_eq_iff_eq_neg.mp h3)

private lemma mismatched_core_HL2 {G : Type*} [AddCommGroup G] {P V P' Q' T R : G}
    (hT : T + T = 0) (h1 : P = P' + T) (h2 : V = -(Q' + T))
    (h5 : R = P + Q' ∨ R = -(P + Q')) (h6 : R = P' + V ∨ R = -(P' + V)) :
    P + P = 0 ∨ V + V = 0 := by
  have key : P + Q' = P' + V ∨ P + Q' = -(P' + V) := by
    rcases h5 with h5 | h5 <;> rcases h6 with h6 | h6
    · exact Or.inl (h5.symm.trans h6)
    · exact Or.inr (h5.symm.trans h6)
    · exact Or.inr (neg_eq_iff_eq_neg.mp (h5.symm.trans h6))
    · exact Or.inl (neg_inj.mp (h5.symm.trans h6))
  rcases key with hk | hk
  ·
    right
    rw [h1, h2] at hk
    have hQQ : Q' + Q' + (T + T) = 0 := by
      have h0 : Q' + Q' + (T + T) = (P' + T + Q') - (P' + -(Q' + T)) := by abel
      rw [hk, sub_self] at h0
      exact h0
    have hQ : Q' + Q' = 0 := by rwa [hT, add_zero] at hQQ
    rw [h2]
    have h0 : -(Q' + T) + -(Q' + T) = -((Q' + Q') + (T + T)) := by abel
    rw [h0, hQ, hT, add_zero, neg_zero]
  ·
    left
    rw [h1, h2] at hk
    have hPP : P' + P' = 0 := by
      have h0 : P' + P' = (P' + T + Q') - -(P' + -(Q' + T)) := by abel
      rw [hk, sub_self] at h0
      exact h0
    rw [h1]
    have h0 : (P' + T) + (P' + T) = (P' + P') + (T + T) := by abel
    rw [h0, hPP, hT, add_zero]

private lemma point_group_analysis_HL2 {G : Type*} [AddCommGroup G] {P V P' Q' T R : G}
    (hT : T + T = 0)
    (h1 : P = P' + T ∨ P = -(P' + T))
    (h2 : V = Q' + T ∨ V = -(Q' + T))
    (h5 : R = P + Q' ∨ R = -(P + Q'))
    (h6 : R = P' + V ∨ R = -(P' + V)) :
    ((P + V = P' + Q' ∨ P + V = -(P' + Q')) ∧ (P - V = P' - Q' ∨ P - V = -(P' - Q'))) ∨
    ((P + V = P' - Q' ∨ P + V = -(P' - Q')) ∧ (P - V = P' + Q' ∨ P - V = -(P' + Q')) ∧
      (P + P = 0 ∨ V + V = 0)) := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  ·
    left
    constructor
    · left
      rw [h1, h2]
      have h0 : P' + T + (Q' + T) = P' + Q' + (T + T) := by abel
      rw [h0, hT, add_zero]
    · left
      rw [h1, h2]; abel
  ·
    right
    refine ⟨Or.inl ?_, Or.inl ?_, mismatched_core_HL2 hT h1 h2 h5 h6⟩
    · rw [h1, h2]; abel
    · rw [h1, h2]
      have h0 : P' + T - -(Q' + T) = P' + Q' + (T + T) := by abel
      rw [h0, hT, add_zero]
  ·
    right
    have h5s : R = V + P' ∨ R = -(V + P') := by
      rcases h6 with h6 | h6
      · exact Or.inl (h6.trans (add_comm P' V))
      · exact Or.inr (h6.trans (neg_inj.mpr (add_comm P' V)))
    have h6s : R = Q' + P ∨ R = -(Q' + P) := by
      rcases h5 with h5 | h5
      · exact Or.inl (h5.trans (add_comm P Q'))
      · exact Or.inr (h5.trans (neg_inj.mpr (add_comm P Q')))
    refine ⟨Or.inr ?_, Or.inr ?_, (mismatched_core_HL2 hT h2 h1 h5s h6s).symm⟩
    · rw [h1, h2]; abel
    · rw [h1, h2]
      have h0 : -(P' + T) - (Q' + T) = -(P' + Q') - (T + T) := by abel
      rw [h0, hT, sub_zero]
  ·
    left
    constructor
    · right
      rw [h1, h2]
      have h0 : -(P' + T) + -(Q' + T) = -(P' + Q') - (T + T) := by abel
      rw [h0, hT, sub_zero]
    · right
      rw [h1, h2]; abel

set_option maxHeartbeats 6400000 in

theorem genericHalfLatticeAddition_of_offLocus_families (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hτ : τ ^ 2 = q)
    (hS1 : ∀ a b : K, AddParams q a b → ¬(OnHalfLattice q a ∧ OnHalfLattice q b) →
      (pointX q (a * b) + pointX q (a * b⁻¹)) * (pointX q a - pointX q b) ^ 2 =
        symSumNum q (pointX q a) (pointX q b))
    (hD1 : ∀ a b : K, AddParams q a b → ¬(OnHalfLattice q a ∧ OnHalfLattice q b) →
      (pointX q (a * b) - pointX q (a * b⁻¹)) * (pointX q a - pointX q b) ^ 2 =
        -((2 * pointY q a + pointX q a) * (2 * pointY q b + pointX q b))) :
    GenericHalfLatticeAddition q τ := by
  intro u v hp hu2 hv2 hu' hv'
  have hq' : ‖q‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]; exact hq
  have ht0 : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0

  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0] at hτ
    exact hq0 (by simpa using hτ.symm)
  have hτi0 : τ⁻¹ ≠ 0 := inv_ne_zero hτ0
  have hτ2 : ‖τ‖ * ‖τ‖ = ‖q‖ := by
    have h1 := congrArg norm hτ
    rwa [norm_pow, sq] at h1
  have hτpos : (0 : ℝ) < ‖τ‖ := norm_pos_iff.mpr hτ0
  have hτlt1 : ‖τ‖ < 1 := by
    by_contra hcon
    have hcon' : (1 : ℝ) ≤ ‖τ‖ := not_lt.mp hcon
    have h1 : (1 : ℝ) * 1 ≤ ‖τ‖ * ‖τ‖ := mul_le_mul hcon' hcon' zero_le_one (norm_nonneg τ)
    rw [hτ2, one_mul] at h1
    linarith
  have hqltτ : ‖q‖ < ‖τ‖ := by
    by_contra hcon
    have hcon' : ‖τ‖ ≤ ‖q‖ := not_lt.mp hcon
    have h1 : ‖τ‖ * ‖τ‖ ≤ ‖q‖ * ‖q‖ := mul_le_mul hcon' hcon' (norm_nonneg τ) (norm_nonneg q)
    rw [hτ2] at h1
    have h2 : ‖q‖ * ‖q‖ < ‖q‖ * 1 := mul_lt_mul_of_pos_left hq ht0
    rw [mul_one] at h2
    linarith
  have hτle1 : ‖τ‖ ≤ 1 := le_of_lt hτlt1
  have hu_eq : ‖u‖ = ‖τ‖ := by
    rcases mul_self_eq_mul_self_iff.mp (hu2.trans hτ2.symm) with h | h
    · exact h
    · exfalso
      have := norm_nonneg u
      linarith
  have hv_eq : ‖v‖ = ‖τ‖ := by
    rcases mul_self_eq_mul_self_iff.mp (hv2.trans hτ2.symm) with h | h
    · exact h
    · exfalso
      have := norm_nonneg v
      linarith
  have hule1 : ‖u‖ ≤ 1 := by rw [hu_eq]; exact hτle1
  have hvle1 : ‖v‖ ≤ 1 := by rw [hv_eq]; exact hτle1
  have hu'1 : ‖u * τ⁻¹‖ = 1 := by
    rw [norm_mul, norm_inv, hu_eq]
    exact mul_inv_cancel₀ (ne_of_gt hτpos)
  have hv'1 : ‖v * τ⁻¹‖ = 1 := by
    rw [norm_mul, norm_inv, hv_eq]
    exact mul_inv_cancel₀ (ne_of_gt hτpos)
  have hu'le1 : ‖u * τ⁻¹‖ ≤ 1 := le_of_eq hu'1
  have hv'le1 : ‖v * τ⁻¹‖ ≤ 1 := le_of_eq hv'1
  have hτinv2 : ‖τ‖⁻¹ * ‖τ‖⁻¹ = ‖q‖⁻¹ := by rw [← mul_inv, hτ2]

  have hu0 : u ≠ 0 := hp.u_ne_zero
  have hv0 : v ≠ 0 := hp.v_ne_zero
  have hu'0 : u * τ⁻¹ ≠ 0 := mul_ne_zero hu0 hτi0
  have hv'0 : v * τ⁻¹ ≠ 0 := mul_ne_zero hv0 hτi0

  have hτOff : OffLattice q τ :=
    offLattice_of_sq_norm_eq_zpow_odd hq0 hq 0
      (by rw [hτ2, show (2 * (0 : ℤ) + 1) = 1 by norm_num, zpow_one])

  have hu'τ : u * τ⁻¹ * τ = u := by
    rw [mul_assoc, inv_mul_cancel₀ hτ0, mul_one]
  have hv'τ : v * τ⁻¹ * τ = v := by
    rw [mul_assoc, inv_mul_cancel₀ hτ0, mul_one]
  have hq_inv : (q : K)⁻¹ = τ⁻¹ * τ⁻¹ := by
    rw [← mul_inv, ← sq, hτ]
  have hu'τinv : u * τ⁻¹ * τ⁻¹ = (q : K) ^ (-1 : ℤ) * u := by
    rw [zpow_neg_one, hq_inv]; ring
  have hv'τinv : v * τ⁻¹ * τ⁻¹ = (q : K) ^ (-1 : ℤ) * v := by
    rw [zpow_neg_one, hq_inv]; ring
  have hu'v' : u * τ⁻¹ * (v * τ⁻¹) = (q : K) ^ (-1 : ℤ) * (u * v) := by
    rw [zpow_neg_one, hq_inv]; ring
  have hu'v'inv : u * τ⁻¹ * (v * τ⁻¹)⁻¹ = u * v⁻¹ := by
    rw [mul_inv, inv_inv]
    calc u * τ⁻¹ * (v⁻¹ * τ) = u * v⁻¹ * (τ⁻¹ * τ) := by ring
      _ = u * v⁻¹ := by rw [inv_mul_cancel₀ hτ0, mul_one]

  have hvinv2 : ‖v‖⁻¹ * ‖v‖⁻¹ = ‖q‖⁻¹ := by rw [← mul_inv, hv2]
  have hmixOff : OffLattice q (u * v * τ⁻¹) := by
    apply offLattice_of_sq_norm_eq_zpow_odd hq0 hq 0
    have h1 : ‖u * v * τ⁻¹‖ * ‖u * v * τ⁻¹‖ =
        (‖u‖ * ‖u‖) * ((‖v‖ * ‖v‖) * (‖τ‖⁻¹ * ‖τ‖⁻¹)) := by
      rw [norm_mul, norm_mul, norm_inv]; ring
    rw [h1, hu2, hv2, hτinv2, show (2 * (0 : ℤ) + 1) = 1 by norm_num, zpow_one,
      mul_inv_cancel₀ (ne_of_gt ht0), mul_one]
  have hmixOff2 : OffLattice q (u * v⁻¹ * τ) := by
    apply offLattice_of_sq_norm_eq_zpow_odd hq0 hq 0
    have h1 : ‖u * v⁻¹ * τ‖ * ‖u * v⁻¹ * τ‖ =
        (‖u‖ * ‖u‖) * ((‖v‖⁻¹ * ‖v‖⁻¹) * (‖τ‖ * ‖τ‖)) := by
      rw [norm_mul, norm_mul, norm_inv]; ring
    rw [h1, hu2, hvinv2, hτ2, show (2 * (0 : ℤ) + 1) = 1 by norm_num, zpow_one,
      inv_mul_cancel₀ (ne_of_gt ht0), mul_one]
  have hmixOff3 : OffLattice q (u * v⁻¹ * τ⁻¹) := by
    apply offLattice_of_sq_norm_eq_zpow_odd hq0 hq (-1)
    have h1 : ‖u * v⁻¹ * τ⁻¹‖ * ‖u * v⁻¹ * τ⁻¹‖ =
        (‖u‖ * ‖u‖) * ((‖v‖⁻¹ * ‖v‖⁻¹) * (‖τ‖⁻¹ * ‖τ‖⁻¹)) := by
      rw [norm_mul, norm_mul, norm_inv, norm_inv]; ring
    rw [h1, hu2, hvinv2, hτinv2, show (2 * (-1 : ℤ) + 1) = -1 by norm_num, zpow_neg_one,
      ← mul_assoc, mul_inv_cancel₀ (ne_of_gt ht0), one_mul]

  have hP1 : AddParams q (u * τ⁻¹) τ :=
    { q_ne_zero := hq0
      u_ne_zero := hu'0
      v_ne_zero := hτ0
      offLattice_u := hu'
      offLattice_v := hτOff
      offLattice_mul := by rw [hu'τ]; exact hp.offLattice_u
      offLattice_div := by rw [hu'τinv]; exact OffLattice.zpow_mul hq0 (-1) hp.offLattice_u }
  have hP2 : AddParams q (v * τ⁻¹) τ :=
    { q_ne_zero := hq0
      u_ne_zero := hv'0
      v_ne_zero := hτ0
      offLattice_u := hv'
      offLattice_v := hτOff
      offLattice_mul := by rw [hv'τ]; exact hp.offLattice_v
      offLattice_div := by rw [hv'τinv]; exact OffLattice.zpow_mul hq0 (-1) hp.offLattice_v }
  have hP3 : AddParams q (u * τ⁻¹) (v * τ⁻¹) :=
    { q_ne_zero := hq0
      u_ne_zero := hu'0
      v_ne_zero := hv'0
      offLattice_u := hu'
      offLattice_v := hv'
      offLattice_mul := by rw [hu'v']; exact OffLattice.zpow_mul hq0 (-1) hp.offLattice_mul
      offLattice_div := by rw [hu'v'inv]; exact hp.offLattice_div }
  have hP5 : AddParams q u (v * τ⁻¹) :=
    { q_ne_zero := hq0
      u_ne_zero := hu0
      v_ne_zero := hv'0
      offLattice_u := hp.offLattice_u
      offLattice_v := hv'
      offLattice_mul := by
        rw [show u * (v * τ⁻¹) = u * v * τ⁻¹ by ring]; exact hmixOff
      offLattice_div := by
        rw [show u * (v * τ⁻¹)⁻¹ = u * v⁻¹ * τ by rw [mul_inv, inv_inv]; ring]
        exact hmixOff2 }
  have hP6 : AddParams q (u * τ⁻¹) v :=
    { q_ne_zero := hq0
      u_ne_zero := hu'0
      v_ne_zero := hv0
      offLattice_u := hu'
      offLattice_v := hp.offLattice_v
      offLattice_mul := by
        rw [show u * τ⁻¹ * v = u * v * τ⁻¹ by ring]; exact hmixOff
      offLattice_div := by
        rw [show u * τ⁻¹ * v⁻¹ = u * v⁻¹ * τ⁻¹ by ring]; exact hmixOff3 }

  have hnotloc_u' : ¬ OnHalfLattice q (u * τ⁻¹) := not_onHalfLattice_of_norm_eq_one hq0 hq hu'1
  have hnotloc_v' : ¬ OnHalfLattice q (v * τ⁻¹) := not_onHalfLattice_of_norm_eq_one hq0 hq hv'1
  have hloc1 : ¬ (OnHalfLattice q (u * τ⁻¹) ∧ OnHalfLattice q τ) := fun h => hnotloc_u' h.1
  have hloc2 : ¬ (OnHalfLattice q (v * τ⁻¹) ∧ OnHalfLattice q τ) := fun h => hnotloc_v' h.1
  have hloc3 : ¬ (OnHalfLattice q (u * τ⁻¹) ∧ OnHalfLattice q (v * τ⁻¹)) :=
    fun h => hnotloc_u' h.1
  have hloc5 : ¬ (OnHalfLattice q u ∧ OnHalfLattice q (v * τ⁻¹)) := fun h => hnotloc_v' h.2
  have hloc6 : ¬ (OnHalfLattice q (u * τ⁻¹) ∧ OnHalfLattice q v) := fun h => hnotloc_u' h.1

  have hxne1 : pointX q (u * τ⁻¹) ≠ pointX q τ :=
    pointX_ne_of_norm_ne hq0 hq hu'0 hτ0 hu' hτOff hu'le1 hτle1
      (by rw [hu'τ, hu_eq]; exact hqltτ)
      (by rw [hu'1]; exact ne_of_gt hτlt1)
      (by rw [hu'τ, hu_eq]; exact ne_of_lt hτlt1)
  have hxne2 : pointX q (v * τ⁻¹) ≠ pointX q τ :=
    pointX_ne_of_norm_ne hq0 hq hv'0 hτ0 hv' hτOff hv'le1 hτle1
      (by rw [hv'τ, hv_eq]; exact hqltτ)
      (by rw [hv'1]; exact ne_of_gt hτlt1)
      (by rw [hv'τ, hv_eq]; exact ne_of_lt hτlt1)
  have hxne5 : pointX q u ≠ pointX q (v * τ⁻¹) :=
    pointX_ne_of_norm_ne hq0 hq hu0 hv'0 hp.offLattice_u hv' hule1 hv'le1
      (by rw [norm_mul, hv'1, mul_one, hu_eq]; exact hqltτ)
      (by rw [hu_eq, hv'1]; exact ne_of_lt hτlt1)
      (by rw [norm_mul, hv'1, mul_one, hu_eq]; exact ne_of_lt hτlt1)
  have hxne6 : pointX q (u * τ⁻¹) ≠ pointX q v :=
    pointX_ne_of_norm_ne hq0 hq hu'0 hv0 hu' hp.offLattice_v hu'le1 hvle1
      (by rw [norm_mul, hu'1, one_mul, hv_eq]; exact hqltτ)
      (by rw [hu'1, hv_eq]; exact ne_of_gt hτlt1)
      (by rw [norm_mul, hu'1, one_mul, hv_eq]; exact ne_of_lt hτlt1)
  have hxne3 : pointX q (u * τ⁻¹) ≠ pointX q (v * τ⁻¹) := by
    intro hX
    have hband : ‖q‖ < ‖u * τ⁻¹ * (v * τ⁻¹)‖ := by
      rw [norm_mul, hu'1, hv'1, mul_one]; exact hq
    rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq' hu'0 hv'0 hu' hv' hu'le1 hv'le1 hband hX
      with h | h
    ·
      have huv : u = v := mul_right_cancel₀ hτi0 h
      apply hp.offLattice_div 0
      rw [zpow_zero, one_mul, huv, mul_inv_cancel₀ hv0]
    ·
      apply hp.offLattice_mul (-1)
      rw [zpow_neg_one]
      calc q⁻¹ * (u * v) = u * τ⁻¹ * (v * τ⁻¹) := by rw [hq_inv]; ring
        _ = 1 := h

  have hnsU : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u) :=
    nonsingular_point hq0 hq' hu0 hp.offLattice_u
  have hnsV : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v) :=
    nonsingular_point hq0 hq' hv0 hp.offLattice_v
  have hnsU' : (curve q).toAffine.Nonsingular (pointX q (u * τ⁻¹)) (pointY q (u * τ⁻¹)) :=
    nonsingular_point hq0 hq' hu'0 hu'
  have hnsV' : (curve q).toAffine.Nonsingular (pointX q (v * τ⁻¹)) (pointY q (v * τ⁻¹)) :=
    nonsingular_point hq0 hq' hv'0 hv'
  have hnsT : (curve q).toAffine.Nonsingular (pointX q τ) (pointY q τ) :=
    nonsingular_point hq0 hq' hτ0 hτOff
  have hns1 : (curve q).toAffine.Nonsingular (pointX q (u * τ⁻¹ * τ)) (pointY q (u * τ⁻¹ * τ)) :=
    nonsingular_point hq0 hq' (mul_ne_zero hu'0 hτ0) hP1.offLattice_mul
  have hns2 : (curve q).toAffine.Nonsingular (pointX q (v * τ⁻¹ * τ)) (pointY q (v * τ⁻¹ * τ)) :=
    nonsingular_point hq0 hq' (mul_ne_zero hv'0 hτ0) hP2.offLattice_mul
  have hnsR : (curve q).toAffine.Nonsingular (pointX q (u * (v * τ⁻¹)))
      (pointY q (u * (v * τ⁻¹))) :=
    nonsingular_point hq0 hq' (mul_ne_zero hu0 hv'0) hP5.offLattice_mul
  have hnsR6 : (curve q).toAffine.Nonsingular (pointX q (u * τ⁻¹ * v))
      (pointY q (u * τ⁻¹ * v)) :=
    nonsingular_point hq0 hq' (mul_ne_zero hu'0 hv0) hP6.offLattice_mul

  have hA1 := point_mul_eq_add_or_neg_of_sum_of_diff (hS1 _ _ hP1 hloc1) (hD1 _ _ hP1 hloc1)
    hP1 hxne1 hns1 hnsU' hnsT
  have e1 : (Point.some (pointX q (u * τ⁻¹ * τ)) (pointY q (u * τ⁻¹ * τ)) hns1 :
      (curve q).toAffine.Point) = Point.some (pointX q u) (pointY q u) hnsU :=
    point_some_congr_HL2 (congrArg (pointX q) hu'τ) (congrArg (pointY q) hu'τ) _ _
  rw [e1] at hA1
  have hA2 := point_mul_eq_add_or_neg_of_sum_of_diff (hS1 _ _ hP2 hloc2) (hD1 _ _ hP2 hloc2)
    hP2 hxne2 hns2 hnsV' hnsT
  have e2 : (Point.some (pointX q (v * τ⁻¹ * τ)) (pointY q (v * τ⁻¹ * τ)) hns2 :
      (curve q).toAffine.Point) = Point.some (pointX q v) (pointY q v) hnsV :=
    point_some_congr_HL2 (congrArg (pointX q) hv'τ) (congrArg (pointY q) hv'τ) _ _
  rw [e2] at hA2
  have hA5 := point_mul_eq_add_or_neg_of_sum_of_diff (hS1 _ _ hP5 hloc5) (hD1 _ _ hP5 hloc5)
    hP5 hxne5 hnsR hnsU hnsV'
  have hA6 := point_mul_eq_add_or_neg_of_sum_of_diff (hS1 _ _ hP6 hloc6) (hD1 _ _ hP6 hloc6)
    hP6 hxne6 hnsR6 hnsU' hnsV
  have e6 : (Point.some (pointX q (u * τ⁻¹ * v)) (pointY q (u * τ⁻¹ * v)) hnsR6 :
      (curve q).toAffine.Point) =
      Point.some (pointX q (u * (v * τ⁻¹))) (pointY q (u * (v * τ⁻¹))) hnsR :=
    point_some_congr_HL2 (congrArg (pointX q) (by ring)) (congrArg (pointY q) (by ring)) _ _
  rw [e6] at hA6

  have hψτ : 2 * pointY q τ + pointX q τ = 0 :=
    psiTwo_eq_zero_of_sq_eq_zpow hq0 hq hτ0 hτOff (k := 1) (by rw [hτ, zpow_one])
  have hTT : (Point.some (pointX q τ) (pointY q τ) hnsT : (curve q).toAffine.Point) +
      Point.some (pointX q τ) (pointY q τ) hnsT = 0 := by
    have hTneg : (Point.some (pointX q τ) (pointY q τ) hnsT : (curve q).toAffine.Point) =
        -Point.some (pointX q τ) (pointY q τ) hnsT := by
      rw [Point.neg_some]
      refine point_some_congr_HL2 rfl ?_ _ _
      simp only [negY, curve_a₁, curve_a₃]
      linear_combination hψτ
    nth_rewrite 2 [hTneg]
    abel

  have hxneuv : pointX q u ≠ pointX q v := by
    intro hX
    have hPV : (Point.some (pointX q u) (pointY q u) hnsU : (curve q).toAffine.Point) =
        Point.some (pointX q v) (pointY q v) hnsV ∨
        (Point.some (pointX q u) (pointY q u) hnsU : (curve q).toAffine.Point) =
        -Point.some (pointX q v) (pointY q v) hnsV := by
      rcases WeierstrassCurve.Affine.Y_eq_of_X_eq hnsU.left hnsV.left hX with hY | hY
      · exact Or.inl (point_some_congr_HL2 hX hY _ _)
      · right
        rw [Point.neg_some]
        exact point_some_congr_HL2 hX hY _ _
    have hP'Q' := eq_or_eq_neg_trans_HL2 hA1 hA2 hPV
    rcases hP'Q' with h | h
    · have hPQ : (Point.some (pointX q (u * τ⁻¹)) (pointY q (u * τ⁻¹)) hnsU' :
          (curve q).toAffine.Point) =
          Point.some (pointX q (v * τ⁻¹)) (pointY q (v * τ⁻¹)) hnsV' := add_right_cancel h
      simp only [Point.some.injEq] at hPQ
      exact hxne3 hPQ.1
    · have h0 : (Point.some (pointX q (u * τ⁻¹)) (pointY q (u * τ⁻¹)) hnsU' +
          Point.some (pointX q τ) (pointY q τ) hnsT : (curve q).toAffine.Point) +
          (Point.some (pointX q (v * τ⁻¹)) (pointY q (v * τ⁻¹)) hnsV' +
            Point.some (pointX q τ) (pointY q τ) hnsT) = 0 := by
        rw [h]; abel
      have h1 : (Point.some (pointX q (u * τ⁻¹)) (pointY q (u * τ⁻¹)) hnsU' :
          (curve q).toAffine.Point) +
          Point.some (pointX q (v * τ⁻¹)) (pointY q (v * τ⁻¹)) hnsV' = 0 := by
        have h2 : (Point.some (pointX q (u * τ⁻¹)) (pointY q (u * τ⁻¹)) hnsU' :
            (curve q).toAffine.Point) +
            Point.some (pointX q (v * τ⁻¹)) (pointY q (v * τ⁻¹)) hnsV' =
            ((Point.some (pointX q (u * τ⁻¹)) (pointY q (u * τ⁻¹)) hnsU' +
              Point.some (pointX q τ) (pointY q τ) hnsT) +
              (Point.some (pointX q (v * τ⁻¹)) (pointY q (v * τ⁻¹)) hnsV' +
                Point.some (pointX q τ) (pointY q τ) hnsT)) -
              (Point.some (pointX q τ) (pointY q τ) hnsT +
                Point.some (pointX q τ) (pointY q τ) hnsT) := by abel
        rw [h0, hTT, sub_zero] at h2
        exact h2
      have h3 : (Point.some (pointX q (u * τ⁻¹)) (pointY q (u * τ⁻¹)) hnsU' :
          (curve q).toAffine.Point) =
          -Point.some (pointX q (v * τ⁻¹)) (pointY q (v * τ⁻¹)) hnsV' :=
        add_eq_zero_iff_eq_neg.mp h1
      rw [Point.neg_some] at h3
      simp only [Point.some.injEq] at h3
      exact hxne3 h3.1

  have hsumG := WeierstrassCurve.Affine.addX_add_addX_negY_mul_sq' (W := curve q)
    hnsU.left hnsV.left hxneuv
  rw [← symSumNum_eq_b] at hsumG
  have hdiffG := WeierstrassCurve.Affine.addX_sub_addX_negY_mul_sq (W := curve q)
    (pointY q u) (pointY q v) hxneuv
  rw [sub_negY_curve, sub_negY_curve] at hdiffG

  have hS1' := hS1 _ _ hP3 hloc3
  have hD1' := hD1 _ _ hP3 hloc3
  have hXm : pointX q (u * τ⁻¹ * (v * τ⁻¹)) = pointX q (u * v) := by
    rw [hu'v', pointX_zpow_mul hq0]
  have hXd : pointX q (u * τ⁻¹ * (v * τ⁻¹)⁻¹) = pointX q (u * v⁻¹) := by
    rw [hu'v'inv]
  rw [hXm, hXd] at hS1' hD1'
  have hsum' := WeierstrassCurve.Affine.addX_add_addX_negY_mul_sq' (W := curve q)
    hnsU'.left hnsV'.left hxne3
  rw [← symSumNum_eq_b] at hsum'
  have hdiff' := WeierstrassCurve.Affine.addX_sub_addX_negY_mul_sq (W := curve q)
    (pointY q (u * τ⁻¹)) (pointY q (v * τ⁻¹)) hxne3
  rw [sub_negY_curve, sub_negY_curve] at hdiff'
  have hd2' : (pointX q (u * τ⁻¹) - pointX q (v * τ⁻¹)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr hxne3)
  have hsumEq' := mul_right_cancel₀ hd2' (hS1'.trans hsum'.symm)
  have hdiffEq' := mul_right_cancel₀ hd2' (hD1'.trans hdiff'.symm)

  have hKey := point_group_analysis_HL2 hTT hA1 hA2 hA5 hA6
  rcases hKey with ⟨hpv, hmv⟩ | ⟨hpv, hmv, h2tor⟩
  ·
    have ha := addX_eq_of_add_eq_or_neg_HL2 hxneuv hxne3 hpv
    simp only [sub_eq_add_neg, Point.neg_some] at hmv
    have hb := addX_eq_of_add_eq_or_neg_HL2 hxneuv hxne3 hmv
    refine ⟨?_, ?_⟩
    · linear_combination hsumG + (pointX q u - pointX q v) ^ 2 * hsumEq' -
        (pointX q u - pointX q v) ^ 2 * ha - (pointX q u - pointX q v) ^ 2 * hb
    · linear_combination hdiffG + (pointX q u - pointX q v) ^ 2 * hdiffEq' -
        (pointX q u - pointX q v) ^ 2 * ha + (pointX q u - pointX q v) ^ 2 * hb
  ·
    simp only [sub_eq_add_neg, Point.neg_some] at hpv
    have ha := addX_eq_of_add_eq_or_neg_HL2 hxneuv hxne3 hpv
    simp only [sub_eq_add_neg, Point.neg_some] at hmv
    have hb := addX_eq_of_add_eq_or_neg_HL2 hxneuv hxne3 hmv
    have hψ : (2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v) = 0 := by
      rcases h2tor with h2t | h2t
      · rw [psiTwo_eq_zero_of_double_eq_zero_HL2 hnsU h2t, zero_mul]
      · rw [psiTwo_eq_zero_of_double_eq_zero_HL2 hnsV h2t, mul_zero]
    refine ⟨?_, ?_⟩
    · linear_combination hsumG + (pointX q u - pointX q v) ^ 2 * hsumEq' -
        (pointX q u - pointX q v) ^ 2 * ha - (pointX q u - pointX q v) ^ 2 * hb
    · linear_combination -hdiffG + (pointX q u - pointX q v) ^ 2 * hdiffEq' +
        (pointX q u - pointX q v) ^ 2 * ha - (pointX q u - pointX q v) ^ 2 * hb + 2 * hψ

theorem genericHalfLatticeAddition_of_region (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v'))) :
    GenericHalfLatticeAddition q τ :=
  genericHalfLatticeAddition_of_offLocus_families hq0 hq hτ
    (fun _ _ hab hnl => symAdd_sum_of_region_of_not_halfLattice hq0 hq hregS1 hab hnl)
    (fun _ _ hab hnl => diff_identity_of_region_of_not_halfLattice hq0 hq hregD1 hab hnl)

theorem symAdd_sum_of_region_closed (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) :=
  symAdd_sum_of_region_all hq0 hq hτ
    (genericHalfLatticeAddition_of_region hq0 hq hτ hregS1 hregD1) hregS1 hregD1 hp

theorem diff_identity_of_region_closed (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v) :
    (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) :=
  diff_identity_of_region_all hq0 hq hτ
    (genericHalfLatticeAddition_of_region hq0 hq hτ hregS1 hregD1) hregS1 hregD1 hp

theorem diffHyp_of_region_closed (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v'))) :
    DiffHyp q :=
  fun _ _ hp => diff_identity_of_region_closed hq0 hq hτ hregS1 hregD1 hp

theorem symAdd_sum_of_region_isAlgClosed [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v) :
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) := by
  obtain ⟨τ, hτ⟩ := exists_sqrt_of_isAlgClosed (K := K) q
  exact symAdd_sum_of_region_closed hq0 hq hτ hregS1 hregD1 hp

theorem diff_identity_of_region_isAlgClosed [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v) :
    (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) := by
  obtain ⟨τ, hτ⟩ := exists_sqrt_of_isAlgClosed (K := K) q
  exact diff_identity_of_region_closed hq0 hq hτ hregS1 hregD1 hp

theorem diffHyp_of_region_isAlgClosed [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v'))) :
    DiffHyp q := by
  obtain ⟨τ, hτ⟩ := exists_sqrt_of_isAlgClosed (K := K) q
  exact diffHyp_of_region_closed hq0 hq hτ hregS1 hregD1

end TateCurve

open _root_.TateCurve _root_.P2MW.S_TateCurve_ks17_D2_exports.TateCurve in
theorem solution :

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] {q τ : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v'))),
      DiffHyp q) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] [IsAlgClosed K] (q : K),
      ∃ τ : K, τ ^ 2 = q) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] {q u v τ : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v),
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = symSumNum q (pointX q u) (pointX q v)) :=
  ⟨@TateCurve.diffHyp_of_region_closed, @TateCurve.exists_sqrt_of_isAlgClosed, @TateCurve.symAdd_sum_of_region_closed⟩

end S_TateCurve_ks17_D2_exports
end P2MW
export P2MW.S_TateCurve_ks17_D2_exports (solution)
