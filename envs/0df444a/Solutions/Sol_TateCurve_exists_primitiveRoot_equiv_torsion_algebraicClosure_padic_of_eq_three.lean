-- Prove2me | solution 1 for TateCurve.exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c0f6c72c-29a2-5697-8197-41a55fbfbe9c

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_Padic_exists_complete_algClosed_isometry_algebraicClosure
import Theorems.Thm_PadicInt_exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_eq_three
p2m_attr_erase "instance" "PadicInt.KummerCarrier.instFreeA PadicInt.KummerCarrier.instFiniteA"

set_option linter.unusedSectionVars false
set_option autoImplicit false

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine

namespace TateCurve
p2m_export "TateCurve" "isElliptic term summable_term coeffSum b a₄ a₆ curve curve_a₁ curve_a₃ tateParam_ne_zero tateParam_pow tateParam_offLattice tateParam_class_eq point_mul_eq_add_of_symAddHyps_of_diffHyp muTranslation_of_symAddHyps_of_diffHyp zeta_pow_mod zeta_pow_point_eq_nsmul nsmul_prime_eq_zero_unconditional eq_zpow_mul_of_pointXY_eq_unconditional tateTorsionPoint tateTorsionPoint_spec tateTorsionPoint_zero_zero tateTorsionPoint_ne_zero nsmul_tateTorsionPoint tateTorsionPoint_injOn tateTorsionEquiv map_pointX_tateParam map_pointY_tateParam eq_or_mul_eq_one_of_pointX_eq nsmul_prime_eq_zero SymAddHyps nonsingular_point OffLattice OffLattice.zpow_mul OffLattice.inv AddParams offLattice_of_norm_eq_one pointX pointY pointX_inv pointX_zpow_mul pointY_inv pointY_zpow_mul DiffHyp MuTranslation symAddHyps_unconditional diffHyp_unconditional"
p2m_open "TateCurve"
namespace EqThree

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u ζ t : K} {p : ℕ}

theorem point_some_congr {W : WeierstrassCurve K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

theorem norm_eq_one_of_isPrimitiveRoot (hζ : IsPrimitiveRoot ζ p) (hp0 : p ≠ 0) :
    ‖ζ‖ = 1 := by
  have h1 : ‖ζ‖ ^ p = 1 := by rw [← norm_pow, hζ.pow_eq_one, norm_one]
  rcases (pow_eq_one_iff_of_ne_zero hp0).mp h1 with h | ⟨h, _⟩
  · exact h
  · exfalso
    have h2 := norm_nonneg ζ
    rw [h] at h2
    linarith

theorem offLattice_zeta_pow' (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) (hζ : IsPrimitiveRoot ζ p)
    (hp0 : p ≠ 0) {k : ℕ} (hk : ¬ p ∣ k) : OffLattice q (ζ ^ k) :=
  offLattice_of_norm_eq_one hq0 hq1
    (by rw [norm_pow, norm_eq_one_of_isPrimitiveRoot hζ hp0, one_pow])
    (fun h1 => hk ((hζ.pow_eq_one_iff_dvd k).mp h1))

theorem point_zpow_mul_inv_eq_neg (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : OffLattice q u) {w : K} {n : ℤ} (hw : w = q ^ n * u⁻¹)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u)) :
    (Point.some (pointX q w) (pointY q w) h₁ : (curve q).toAffine.Point)
      = -Point.some (pointX q u) (pointY q u) h₂ := by
  have hX : pointX q w = pointX q u := by
    rw [hw, pointX_zpow_mul hq0, pointX_inv hq0 hu0 hu]
  have hY : pointY q w = -pointY q u - pointX q u := by
    rw [hw, pointY_zpow_mul hq0, pointY_inv hq0 hq hu0 hu]
  rw [Point.neg_some]
  refine point_some_congr hX ?_ h₁ _
  rw [hY, negY]
  show -pointY q u - pointX q u = -pointY q u - (curve q).a₁ * pointX q u - (curve q).a₃
  rw [curve_a₁, curve_a₃]
  ring

theorem sq_point_eq_add_self_of_pow_three [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hp3 : p = 3) (hu0 : u ≠ 0) (hu : OffLattice q u) {s : ℤ} (hpow : u ^ p = q ^ s)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (u * u)) (pointY q (u * u)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u)) :
    (Point.some (pointX q (u * u)) (pointY q (u * u)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q u) (pointY q u) h₂ + Point.some (pointX q u) (pointY q u) h₂ := by
  subst hp3

  have hcube : u * u * u = q ^ s := by rw [← hpow]; ring
  have hw : u * u = q ^ s * u⁻¹ := (eq_mul_inv_iff_mul_eq₀ hu0).mpr hcube
  have hneg := point_zpow_mul_inv_eq_neg hq0 hq hu0 hu hw h₁ h₂

  have h3 : 3 • (Point.some (pointX q u) (pointY q u) h₂ : (curve q).toAffine.Point) = 0 :=
    nsmul_prime_eq_zero_unconditional hq0 hq hu0 hu hpow Nat.prime_three (by decide) h₂
  set P := (Point.some (pointX q u) (pointY q u) h₂ : (curve q).toAffine.Point) with hP
  have h3' : P + P + P = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul] at h3
    exact h3
  rw [hneg]
  exact (eq_neg_of_add_eq_zero_left h3').symm

def MuDoubling (q ζ : K) (p : ℕ) : Prop :=
  ∀ a : ℕ, 1 ≤ a → a < p →
    ∀ (h₁ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a * ζ ^ a)) (pointY q (ζ ^ a * ζ ^ a)))
      (h₂ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a)) (pointY q (ζ ^ a))),
      (Point.some (pointX q (ζ ^ a * ζ ^ a)) (pointY q (ζ ^ a * ζ ^ a)) h₁ :
          (curve q).toAffine.Point)
        = Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂
            + Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂

theorem muTranslation_aux (hyps : SymAddHyps q) (hdiff : DiffHyp q)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hpp : p.Prime) (hodd : Odd p)
    (hζ : IsPrimitiveRoot ζ p) (hdbl : MuDoubling q ζ p) {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p)
    {u : K} (hu0 : u ≠ 0) (hu : OffLattice q u) (hau : OffLattice q (ζ ^ a * u))
    (hule : ‖u‖ ≤ 1) (hqlt : ‖q‖ < ‖u‖)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a)) (pointY q (ζ ^ a)))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u)) :
    (Point.some (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂
          + Point.some (pointX q u) (pointY q u) h₃ := by

  have hp0 : p ≠ 0 := hpp.ne_zero
  have hp3 : 3 ≤ p := by
    have h2 := hpp.two_le
    obtain ⟨k, hk⟩ := hodd
    omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp0
  have hζa0 : ζ ^ a ≠ 0 := pow_ne_zero _ hζ0
  have hq1 : ‖q‖ < 1 := by exact_mod_cast hq
  have hnζ : ‖ζ‖ = 1 := norm_eq_one_of_isPrimitiveRoot hζ hp0
  have hnζa : ‖ζ ^ a‖ = 1 := by rw [norm_pow, hnζ, one_pow]
  have hndvd_a : ¬ p ∣ a := fun hdvd =>
    absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have hndvd_2a : ¬ p ∣ a + a := by
    intro hdvd
    rw [← two_mul a] at hdvd
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h2 | ha
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact hndvd_a ha
  have hζaOff : OffLattice q (ζ ^ a) := offLattice_zeta_pow' hq0 hq1 hζ hp0 hndvd_a
  have hζ2aOff : OffLattice q (ζ ^ a * ζ ^ a) := by
    rw [← pow_add]
    exact offLattice_zeta_pow' hq0 hq1 hζ hp0 hndvd_2a

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
      have hdouble := hdbl a ha1 hap hDns h₂
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

      have hL : (Point.some (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)) h₁ :
          (curve q).toAffine.Point)
          = -(Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂) :=
        point_zpow_mul_inv_eq_neg hq0 hq hζa0 hζaOff hzu_eq h₁ h₂
      have hU : (Point.some (pointX q u) (pointY q u) h₃ : (curve q).toAffine.Point)
          = -(Point.some (pointX q (ζ ^ a * ζ ^ a)) (pointY q (ζ ^ a * ζ ^ a)) hDns) :=
        point_zpow_mul_inv_eq_neg hq0 hq (mul_ne_zero hζa0 hζa0) hζ2aOff hu_eq h₃ hDns
      rw [hL, hU, hdouble]
      abel
  ·

    have hdouble := hdbl a ha1 hap hDns h₂
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
      point_some_congr hXzu hYzu h₁ hDns
    have hU : (Point.some (pointX q u) (pointY q u) h₃ : (curve q).toAffine.Point)
        = Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂ :=
      point_some_congr hXu hYu h₃ h₂
    rw [hL, hU]
    exact hdouble

theorem muTranslation_of_muDoubling (hyps : SymAddHyps q) (hdiff : DiffHyp q)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hpp : p.Prime) (hodd : Odd p)
    (hζ : IsPrimitiveRoot ζ p) (hdbl : MuDoubling q ζ p) :
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

  have haux := muTranslation_aux hyps hdiff hq0 hq hpp hodd hζ hdbl ha1 hap hu'0 hu' hau'
    hu'le hu'gt h₁' h₂ h₃'
  have e₁ : (Point.some (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)) h₁ :
      (curve q).toAffine.Point)
      = Point.some (pointX q (ζ ^ a * u')) (pointY q (ζ ^ a * u')) h₁' :=
    point_some_congr hXzu'.symm hYzu'.symm h₁ h₁'
  have e₃ : (Point.some (pointX q u) (pointY q u) h₃ : (curve q).toAffine.Point)
      = Point.some (pointX q u') (pointY q u') h₃' :=
    point_some_congr hXu'.symm hYu'.symm h₃ h₃'
  rw [e₁, e₃]
  exact haux

theorem muDoubling_of_eq_three [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp3 : p = 3)
    (hζ : IsPrimitiveRoot ζ p) : MuDoubling q ζ p := by
  intro a ha1 hap h₁ h₂
  have hpp : p.Prime := by rw [hp3]; exact Nat.prime_three
  have hp0 : p ≠ 0 := hpp.ne_zero
  have hq1 : ‖q‖ < 1 := by exact_mod_cast hq
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp0
  have hndvd_a : ¬ p ∣ a := fun hdvd =>
    absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have hζaOff : OffLattice q (ζ ^ a) := offLattice_zeta_pow' hq0 hq1 hζ hp0 hndvd_a
  have hpow : (ζ ^ a) ^ p = q ^ (0 : ℤ) := by
    rw [← pow_mul, mul_comm a p, pow_mul, hζ.pow_eq_one, one_pow, zpow_zero]
  exact sq_point_eq_add_self_of_pow_three hq0 hq hp3 (pow_ne_zero _ hζ0) hζaOff hpow h₁ h₂

theorem muTranslation_of_eq_three [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hp3 : p = 3) (hζ : IsPrimitiveRoot ζ p) : MuTranslation q ζ p :=
  muTranslation_of_muDoubling (symAddHyps_unconditional hq0 hq)
    (diffHyp_unconditional hq0 (by exact_mod_cast hq)) hq0 hq (by rw [hp3]; exact Nat.prime_three)
    (by rw [hp3]; decide) hζ (muDoubling_of_eq_three hq0 hq hp3 hζ)

end EqThree
end TateCurve

namespace TateCurve
p2m_export "TateCurve" "isElliptic term summable_term coeffSum b a₄ a₆ curve curve_a₁ curve_a₃ tateParam_ne_zero tateParam_pow tateParam_offLattice tateParam_class_eq point_mul_eq_add_of_symAddHyps_of_diffHyp muTranslation_of_symAddHyps_of_diffHyp zeta_pow_mod zeta_pow_point_eq_nsmul nsmul_prime_eq_zero_unconditional eq_zpow_mul_of_pointXY_eq_unconditional tateTorsionPoint tateTorsionPoint_spec tateTorsionPoint_zero_zero tateTorsionPoint_ne_zero nsmul_tateTorsionPoint tateTorsionPoint_injOn tateTorsionEquiv map_pointX_tateParam map_pointY_tateParam eq_or_mul_eq_one_of_pointX_eq nsmul_prime_eq_zero SymAddHyps nonsingular_point OffLattice OffLattice.zpow_mul OffLattice.inv AddParams offLattice_of_norm_eq_one pointX pointY pointX_inv pointX_zpow_mul pointY_inv pointY_zpow_mul DiffHyp MuTranslation symAddHyps_unconditional diffHyp_unconditional"
p2m_open "TateCurve"
namespace EqThree

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K] [IsAlgClosed K]
variable {q ζ t : K} {p : ℕ}

theorem troot_ne_zero (hq0 : q ≠ 0) (hp : p.Prime) (ht : t ^ p = q) : t ≠ 0 := by
  intro h0
  exact hq0 (by rw [← ht, h0, zero_pow hp.ne_zero])

theorem nsmul_ttp (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp : p.Prime) (hp3 : p = 3)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) (i j : ℕ) :
    p • tateTorsionPoint q ζ t hq0 hq hp hζ ht i j = 0 := by
  have hodd : Odd p := by rw [hp3]; decide
  by_cases hij : i < p ∧ j < p ∧ ¬(i = 0 ∧ j = 0)
  · rw [tateTorsionPoint_spec hq0 hq hp hζ ht hij.1 hij.2.1 hij.2.2]
    exact nsmul_prime_eq_zero_unconditional hq0 hq
      (tateParam_ne_zero (hζ.ne_zero hp.ne_zero) (troot_ne_zero hq0 hp ht))
      (tateParam_offLattice hq0 hq hζ ht hij.1 hij.2.1 hij.2.2)
      (tateParam_pow hζ.pow_eq_one ht i j) hp hodd _
  · rw [tateTorsionPoint, dif_neg hij, smul_zero]

theorem ttp_mem (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp : p.Prime) (hp3 : p = 3)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) (i j : ℕ) :
    tateTorsionPoint q ζ t hq0 hq hp hζ ht i j
      ∈ Submodule.torsionBy ℤ (curve q).toAffine.Point p := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  exact nsmul_ttp hq0 hq hp hp3 hζ ht i j

theorem ttp_injOn (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp : p.Prime) (hp3 : p = 3)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    {i j i' j' : ℕ} (hi : i < p) (hj : j < p) (hi' : i' < p) (hj' : j' < p)
    (hpp : tateTorsionPoint q ζ t hq0 hq hp hζ ht i j
      = tateTorsionPoint q ζ t hq0 hq hp hζ ht i' j') : i = i' ∧ j = j' := by
  have hodd : Odd p := by rw [hp3]; decide
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have ht0 : t ≠ 0 := troot_ne_zero hq0 hp ht
  by_cases hij : i = 0 ∧ j = 0
  · by_cases hij' : i' = 0 ∧ j' = 0
    · exact ⟨hij.1.trans hij'.1.symm, hij.2.trans hij'.2.symm⟩
    · exfalso
      rw [hij.1, hij.2, tateTorsionPoint_zero_zero] at hpp
      exact tateTorsionPoint_ne_zero hq0 hq hp hζ ht hi' hj' hij' hpp.symm
  · by_cases hij' : i' = 0 ∧ j' = 0
    · exfalso
      rw [hij'.1, hij'.2, tateTorsionPoint_zero_zero] at hpp
      exact tateTorsionPoint_ne_zero hq0 hq hp hζ ht hi hj hij hpp
    · rw [tateTorsionPoint_spec hq0 hq hp hζ ht hi hj hij,
        tateTorsionPoint_spec hq0 hq hp hζ ht hi' hj' hij', Point.some.injEq] at hpp
      obtain ⟨k, hk⟩ := eq_zpow_mul_of_pointXY_eq_unconditional hq0 hq
        (tateParam_ne_zero hζ0 ht0) (tateParam_ne_zero hζ0 ht0)
        (tateParam_offLattice hq0 hq hζ ht hi hj hij)
        (tateParam_offLattice hq0 hq hζ ht hi' hj' hij')
        (tateParam_pow hζ.pow_eq_one ht i j) (tateParam_pow hζ.pow_eq_one ht i' j')
        hp hodd hpp.1 hpp.2
      exact tateParam_class_eq hq0 hq hζ ht ht0 hi hj hi' hj' hk

theorem ttp_decomp (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) (hp : p.Prime) (hp3 : p = 3)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    {i j : ℕ} (hi : i < p) (hj : j < p) :
    tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i j
      = tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i 0
        + tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 j := by
  rcases Nat.eq_zero_or_pos i with hi0 | hi1
  · rw [hi0, tateTorsionPoint_zero_zero, zero_add]
  · rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · rw [hj0, tateTorsionPoint_zero_zero, add_zero]
    · have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
      have ht0 : t ≠ 0 := troot_ne_zero hq0 hp ht
      have htj0 : t ^ j ≠ 0 := pow_ne_zero j ht0
      have hij : ¬(i = 0 ∧ j = 0) := by omega
      have hi00 : ¬(i = 0 ∧ (0 : ℕ) = 0) := by omega
      have h0j : ¬((0 : ℕ) = 0 ∧ j = 0) := by omega
      have hparam_i0 : ζ ^ i * t ^ 0 = ζ ^ i := by rw [pow_zero, mul_one]
      have hparam_0j : ζ ^ 0 * t ^ j = t ^ j := by rw [pow_zero, one_mul]
      have htj_off : OffLattice q (t ^ j) := by
        have h := tateParam_offLattice (q := q) hq0 hq1 hζ ht (i := 0) (j := j) hp.pos hj h0j
        rwa [hparam_0j] at h
      have hζi_off : OffLattice q (ζ ^ i) := by
        have h := tateParam_offLattice (q := q) hq0 hq1 hζ ht (i := i) (j := 0) hi hp.pos hi00
        rwa [hparam_i0] at h
      have hζitj_off : OffLattice q (ζ ^ i * t ^ j) :=
        tateParam_offLattice (q := q) hq0 hq1 hζ ht hi hj hij
      have h₁ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ i * t ^ j))
          (pointY q (ζ ^ i * t ^ j)) :=
        nonsingular_point hq0 hq1 (tateParam_ne_zero hζ0 ht0) hζitj_off
      have h₂ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ i)) (pointY q (ζ ^ i)) :=
        nonsingular_point hq0 hq1 (pow_ne_zero i hζ0) hζi_off
      have h₃ : (curve q).toAffine.Nonsingular (pointX q (t ^ j)) (pointY q (t ^ j)) :=
        nonsingular_point hq0 hq1 htj0 htj_off
      have hmain := muTranslation_of_eq_three hq0 hq1 hp3 hζ i hi1 hi (t ^ j)
        htj0 htj_off hζitj_off h₁ h₂ h₃
      have eij : tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i j
          = Point.some (pointX q (ζ ^ i * t ^ j)) (pointY q (ζ ^ i * t ^ j)) h₁ := by
        rw [tateTorsionPoint_spec hq0 hq1 hp hζ ht hi hj hij]
      have ei0 : tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i 0
          = Point.some (pointX q (ζ ^ i)) (pointY q (ζ ^ i)) h₂ := by
        rw [tateTorsionPoint_spec hq0 hq1 hp hζ ht hi hp.pos hi00]
        exact point_some_congr (congrArg (pointX q) hparam_i0) (congrArg (pointY q) hparam_i0) _ h₂
      have e0j : tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 j
          = Point.some (pointX q (t ^ j)) (pointY q (t ^ j)) h₃ := by
        rw [tateTorsionPoint_spec hq0 hq1 hp hζ ht hp.pos hj h0j]
        exact point_some_congr (congrArg (pointX q) hparam_0j) (congrArg (pointY q) hparam_0j) _ h₃
      rw [eij, ei0, e0j]
      exact hmain

theorem ttp_fst_eq_nsmul (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) (hp : p.Prime) (hp3 : p = 3)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) {i : ℕ} (hi : i < p) :
    tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i 0
      = i • tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 1 0 := by
  rcases Nat.eq_zero_or_pos i with hi0 | hi1
  · rw [hi0, tateTorsionPoint_zero_zero, zero_nsmul]
  · have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
    have h10 : ¬((1 : ℕ) = 0 ∧ (0 : ℕ) = 0) := by omega
    have hi0' : ¬(i = 0 ∧ (0 : ℕ) = 0) := by omega
    have hparamζ : ζ ^ 1 * t ^ 0 = ζ := by rw [pow_one, pow_zero, mul_one]
    have hparamζi : ζ ^ i * t ^ 0 = ζ ^ i := by rw [pow_zero, mul_one]
    have hζoff : OffLattice q ζ := by
      have h := tateParam_offLattice (q := q) hq0 hq1 hζ ht (i := 1) (j := 0)
        hp.one_lt hp.pos h10
      rwa [hparamζ] at h
    have hζns : (curve q).toAffine.Nonsingular (pointX q ζ) (pointY q ζ) :=
      nonsingular_point hq0 hq1 hζ0 hζoff
    have hζi_off : OffLattice q (ζ ^ i) := by
      have h := tateParam_offLattice (q := q) hq0 hq1 hζ ht hi hp.pos hi0'
      rwa [hparamζi] at h
    have hζi_ns : (curve q).toAffine.Nonsingular (pointX q (ζ ^ i)) (pointY q (ζ ^ i)) :=
      nonsingular_point hq0 hq1 (pow_ne_zero i hζ0) hζi_off
    have eP1 : tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 1 0
        = Point.some (pointX q ζ) (pointY q ζ) hζns := by
      rw [tateTorsionPoint_spec hq0 hq1 hp hζ ht hp.one_lt hp.pos h10]
      exact point_some_congr (congrArg (pointX q) hparamζ) (congrArg (pointY q) hparamζ) _ hζns
    have ePi : tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i 0
        = Point.some (pointX q (ζ ^ i)) (pointY q (ζ ^ i)) hζi_ns := by
      rw [tateTorsionPoint_spec hq0 hq1 hp hζ ht hi hp.pos hi0']
      exact point_some_congr (congrArg (pointX q) hparamζi) (congrArg (pointY q) hparamζi) _ hζi_ns
    rw [eP1, ePi]
    exact zeta_pow_point_eq_nsmul (muTranslation_of_eq_three hq0 hq1 hp3 hζ) hq0 hq1 hp hζ ht
      hζns i hi1 hi hζi_ns

theorem ttp_snd_eq_nsmul (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) (hp : p.Prime) (hp3 : p = 3)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) {j : ℕ} (hj : j < p) :
    tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 j
      = j • tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 1 := by
  have ht0 : t ≠ 0 := troot_ne_zero hq0 hp ht
  have h01 : ¬((0 : ℕ) = 0 ∧ (1 : ℕ) = 0) := by omega
  have hparam1 : ζ ^ 0 * t ^ 1 = t := by rw [pow_zero, one_mul, pow_one]
  have htoff : OffLattice q t := by
    have h := tateParam_offLattice (q := q) hq0 hq1 hζ ht (i := 0) (j := 1) hp.pos hp.one_lt h01
    rwa [hparam1] at h
  have htns : (curve q).toAffine.Nonsingular (pointX q t) (pointY q t) :=
    nonsingular_point hq0 hq1 ht0 htoff
  have eP1 : tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 1
      = Point.some (pointX q t) (pointY q t) htns := by
    rw [tateTorsionPoint_spec hq0 hq1 hp hζ ht hp.pos hp.one_lt h01]
    exact point_some_congr (congrArg (pointX q) hparam1) (congrArg (pointY q) hparam1) _ htns
  rcases j with _ | _ | _ | j
  · rw [tateTorsionPoint_zero_zero, zero_nsmul]
  · rw [one_nsmul]
  ·
    have h2p : 2 < p := by omega
    have h02 : ¬((0 : ℕ) = 0 ∧ (2 : ℕ) = 0) := by omega
    have hparam2 : ζ ^ 0 * t ^ 2 = t * t := by rw [pow_zero, one_mul, sq]
    have httoff : OffLattice q (t * t) := by
      have h := tateParam_offLattice (q := q) hq0 hq1 hζ ht (i := 0) (j := 2) hp.pos h2p h02
      rwa [hparam2] at h
    have httns : (curve q).toAffine.Nonsingular (pointX q (t * t)) (pointY q (t * t)) :=
      nonsingular_point hq0 hq1 (mul_ne_zero ht0 ht0) httoff
    have eP2 : tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 2
        = Point.some (pointX q (t * t)) (pointY q (t * t)) httns := by
      rw [tateTorsionPoint_spec hq0 hq1 hp hζ ht hp.pos h2p h02]
      exact point_some_congr (congrArg (pointX q) hparam2) (congrArg (pointY q) hparam2) _ httns
    have hpow : t ^ p = q ^ (1 : ℤ) := by rw [ht, zpow_one]
    rw [eP2, eP1, two_nsmul]
    exact sq_point_eq_add_self_of_pow_three hq0 hq1 hp3 ht0 htoff hpow httns htns
  · exfalso; omega

theorem nsmul_mod_of_nsmul_eq_zero {A : Type*} [AddCommGroup A] {P : A} {n m : ℕ}
    (hP : m • P = 0) : (n % m) • P = n • P := by
  have h2 : (n / m * m) • P = 0 := by rw [← smul_smul, hP, smul_zero]
  have key : n = n % m + n / m * m := by
    rw [Nat.mul_comm]; exact (Nat.mod_add_div n m).symm
  conv_rhs => rw [key, add_nsmul, h2, add_zero]

theorem ttp_linearize (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) (hp : p.Prime) (hp3 : p = 3)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) {i j : ℕ} (hi : i < p) (hj : j < p) :
    tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i j
      = i • tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 1 0
        + j • tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 1 := by
  rw [ttp_decomp hq0 hq1 hp hp3 hζ ht hi hj, ttp_fst_eq_nsmul hq0 hq1 hp hp3 hζ ht hi,
    ttp_snd_eq_nsmul hq0 hq1 hp hp3 hζ ht hj]

theorem ttp_add_mod (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) (hp : p.Prime) (hp3 : p = 3)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) {i j i' j' : ℕ}
    (hi : i < p) (hj : j < p) (hi' : i' < p) (hj' : j' < p) :
    tateTorsionPoint q ζ t hq0 hq1 hp hζ ht ((i + i') % p) ((j + j') % p)
      = tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i j
        + tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i' j' := by
  rw [ttp_linearize hq0 hq1 hp hp3 hζ ht (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos),
    ttp_linearize hq0 hq1 hp hp3 hζ ht hi hj, ttp_linearize hq0 hq1 hp hp3 hζ ht hi' hj',
    nsmul_mod_of_nsmul_eq_zero (nsmul_ttp hq0 hq1 hp hp3 hζ ht 1 0),
    nsmul_mod_of_nsmul_eq_zero (nsmul_ttp hq0 hq1 hp hp3 hζ ht 0 1), add_nsmul, add_nsmul]
  abel

theorem torsionMap_bijective (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp : p.Prime) (hp3 : p = 3)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) :
    Function.Bijective (fun ij : Fin p × Fin p =>
      (⟨tateTorsionPoint q ζ t hq0 hq hp hζ ht (ij.1 : ℕ) (ij.2 : ℕ),
        ttp_mem hq0 hq hp hp3 hζ ht (ij.1 : ℕ) (ij.2 : ℕ)⟩ : (curve q).n_torsionGen p)) := by
  have hinj : Function.Injective (fun ij : Fin p × Fin p =>
      (⟨tateTorsionPoint q ζ t hq0 hq hp hζ ht (ij.1 : ℕ) (ij.2 : ℕ),
        ttp_mem hq0 hq hp hp3 hζ ht (ij.1 : ℕ) (ij.2 : ℕ)⟩ : (curve q).n_torsionGen p)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hff
    obtain ⟨h1, h2⟩ := ttp_injOn hq0 hq hp hp3 hζ ht i.isLt j.isLt i'.isLt j'.isLt
      (congrArg Subtype.val hff)
    rw [Prod.mk.injEq]
    exact ⟨Fin.ext h1, Fin.ext h2⟩
  haveI : (curve q).IsElliptic := isElliptic hq0 hq
  have hpK : ((p : ℕ) : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcard : Nat.card ((curve q).n_torsionGen p) = p ^ 2 := by
    have h := WeierstrassCurve.card_torsion_of_isAlgClosed (F := K) (K := K) (curve q) hpK
    have hE : ((curve q)⁄K : WeierstrassCurve K) = curve q := by
      show (curve q).map (algebraMap K K) = curve q
      rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]
    rw [hE] at h
    exact h
  haveI : Finite ((curve q).n_torsionGen p) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  refine hinj.bijective_of_nat_card_le ?_
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, sq]

end EqThree
end TateCurve

namespace TateCurve
p2m_export "TateCurve" "isElliptic term summable_term coeffSum b a₄ a₆ curve curve_a₁ curve_a₃ tateParam_ne_zero tateParam_pow tateParam_offLattice tateParam_class_eq point_mul_eq_add_of_symAddHyps_of_diffHyp muTranslation_of_symAddHyps_of_diffHyp zeta_pow_mod zeta_pow_point_eq_nsmul nsmul_prime_eq_zero_unconditional eq_zpow_mul_of_pointXY_eq_unconditional tateTorsionPoint tateTorsionPoint_spec tateTorsionPoint_zero_zero tateTorsionPoint_ne_zero nsmul_tateTorsionPoint tateTorsionPoint_injOn tateTorsionEquiv map_pointX_tateParam map_pointY_tateParam eq_or_mul_eq_one_of_pointX_eq nsmul_prime_eq_zero SymAddHyps nonsingular_point OffLattice OffLattice.zpow_mul OffLattice.inv AddParams offLattice_of_norm_eq_one pointX pointY pointX_inv pointX_zpow_mul pointY_inv pointY_zpow_mul DiffHyp MuTranslation symAddHyps_unconditional diffHyp_unconditional"
p2m_open "TateCurve"
namespace EqThree

section MapCurve

variable {K₁ : Type*} [NontriviallyNormedField K₁] [IsUltrametricDist K₁]
variable {K₂ : Type*} [NontriviallyNormedField K₂] [IsUltrametricDist K₂]

theorem map_tsum_of_summable₂ {ι : Type*} (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {f : ι → K₁}
    (hf : Summable f) : σ (∑' i, f i) = ∑' i, σ (f i) := by
  have h := hf.hasSum.map σ hσ.continuous
  simpa [Function.comp] using h.tsum_eq.symm

theorem map_term₂ (σ : K₁ →+* K₂) (q : K₁) (c : ℕ → ℕ) (n : ℕ) :
    σ (term c q n) = term c (σ q) n := by
  simp only [term, map_mul, map_natCast, map_div₀, map_pow, map_sub, map_one]

variable [CompleteSpace K₁] [CompleteSpace K₂]

theorem map_coeffSum₂ (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {q : K₁} (hq : ‖q‖₊ < 1) (c : ℕ → ℕ) :
    σ (coeffSum c q) = coeffSum c (σ q) := by
  rw [coeffSum, coeffSum, map_tsum_of_summable₂ σ hσ (summable_term c hq)]
  exact tsum_congr fun n => map_term₂ σ q c n

theorem map_curve₂ (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {q : K₁} (hq : ‖q‖₊ < 1) :
    (curve q).map σ = curve (σ q) := by
  have h4 : σ (a₄ q) = a₄ (σ q) := by
    simp only [a₄, map_neg]
    exact congrArg Neg.neg (map_coeffSum₂ σ hσ hq _)
  have h6 : σ (a₆ q) = a₆ (σ q) := by
    simp only [a₆, map_neg]
    exact congrArg Neg.neg (map_coeffSum₂ σ hσ hq _)
  ext <;> simp [curve, WeierstrassCurve.map, h4, h6]

end MapCurve

section Transport

variable {K : Type} [Field K] [DecidableEq K]

noncomputable def torsionByAddEquivOfEq {W W' : WeierstrassCurve K} (h : W = W') (p : ℕ) :
    W.n_torsionGen p ≃+ W'.n_torsionGen p := by
  subst h; exact AddEquiv.refl _

theorem torsionByAddEquivOfEq_symm_apply_val {W W' : WeierstrassCurve K} (h : W = W')
    (p : ℕ) (P : W'.n_torsionGen p) :
    (((torsionByAddEquivOfEq h p).symm P : W.n_torsionGen p) : W.toAffine.Point)
      = h.symm ▸ (P : W'.toAffine.Point) := by
  subst h; rfl

theorem transport_point_some {W W' : WeierstrassCurve K} (h : W = W')
    {x y : K} (hns : W'.toAffine.Nonsingular x y) :
    (h.symm ▸ (Point.some x y hns : W'.toAffine.Point) : W.toAffine.Point)
      = Point.some x y (h.symm ▸ hns) := by
  subst h; rfl

theorem transport_point_zero {W W' : WeierstrassCurve K} (h : W = W') :
    (h.symm ▸ (0 : W'.toAffine.Point) : W.toAffine.Point) = 0 := by
  subst h; rfl

theorem transport_nonsingular {W W' : WeierstrassCurve K} (h : W = W')
    {x y : K} (hns : W'.toAffine.Nonsingular x y) :
    W.toAffine.Nonsingular x y := by
  subst h; exact hns

end Transport

theorem exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_eq_three
    (p : ℕ) [Fact p.Prime] (hp3 : p = 3) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (ζ t : AlgebraicClosure ℚ_[p]), IsPrimitiveRoot ζ p ∧
      t ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) qT ∧
    ∃ φ : (ZMod p × ZMod p) ≃
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
      (∀ a b, (φ (a + b) : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
              = (φ a : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
              + (φ b : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)) ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (e c : ℕ),
        σ ζ = ζ ^ e → σ t = ζ ^ c * t →
        ∀ i j : ZMod p, σ • (φ (i, j)) = φ (e • i + c • j, j) := by
  letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨K, instNF, instUM, instCS, instCZ, instAC, instAlg, hiso, ι, hext⟩ :=
    Padic.exists_complete_algClosed_isometry_algebraicClosure p
  letI := instNF; letI := instUM; letI := instCS; letI := instCZ; letI := instAC; letI := instAlg
  letI : DecidableEq K := Classical.decEq _

  set qBar := algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) qT with hqBar_def
  have hqBar0 : qBar ≠ 0 :=
    fun h => hqT0 <| (algebraMap ℚ_[p] _).injective (h.trans (map_zero _).symm)
  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ_[p]) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ζ, hζroot⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p (AlgebraicClosure ℚ_[p]))
    (Polynomial.degree_cyclotomic_pos p _ hp.pos).ne'
  have hζ : IsPrimitiveRoot ζ p := Polynomial.isRoot_cyclotomic_iff.mp hζroot
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq qBar (n := p) hp.pos
  refine ⟨ζ, t, hζ, ht, ?_⟩

  set q_K := algebraMap ℚ_[p] K qT with hq_K_def
  have hq_K0 : q_K ≠ 0 :=
    fun h => hqT0 <| (algebraMap ℚ_[p] K).injective (h.trans (map_zero _).symm)
  have hq_K1 : ‖q_K‖₊ < 1 := by
    have h : ‖q_K‖ < 1 := by rw [hq_K_def, hiso]; exact_mod_cast hqT1
    exact_mod_cast h
  have hιinj : Function.Injective ι := RingHom.injective ι.toRingHom
  set ζ_K := ι ζ with hζ_K_def
  set t_K := ι t with ht_K_def
  have hζ_K : IsPrimitiveRoot ζ_K p := hζ.map_of_injective hιinj
  have ht_K : t_K ^ p = q_K := by
    rw [ht_K_def, ← map_pow, ht, hqBar_def, hq_K_def]; exact ι.commutes qT
  have hζ_K0 : ζ_K ≠ 0 := hζ_K.ne_zero hp.ne_zero
  have ht_K0 : t_K ≠ 0 := fun h0 => hq_K0 (by rw [← ht_K, h0, zero_pow hp.ne_zero])

  have hf_isom : Isometry ⇑(algebraMap ℚ_[p] K) := AddMonoidHomClass.isometry_of_norm _ hiso
  have hcurve_eq' : ((TateCurve.curve qT)⁄K : WeierstrassCurve K) = TateCurve.curve q_K :=
    map_curve₂ (algebraMap ℚ_[p] K) hf_isom hqT1
  let br₁Fwd : Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p →+
               Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄K).Point p :=
    { toFun := fun P =>
        ⟨Point.map ι (P : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point),
          by
            rw [Submodule.mem_torsionBy_iff, ← AddMonoidHom.map_zsmul,
              (Submodule.mem_torsionBy_iff _ _).mp P.property, AddMonoidHom.map_zero]⟩
      map_zero' := Subtype.ext (AddMonoidHom.map_zero _)
      map_add' := fun P Q => Subtype.ext (AddMonoidHom.map_add _ _ _) }
  have hbij : Function.Bijective br₁Fwd := by
    have hinj : Function.Injective br₁Fwd := fun P Q hPQ =>
      Subtype.ext (WeierstrassCurve.Affine.Point.map_injective ι (congrArg Subtype.val hPQ))
    haveI : (TateCurve.curve qT).IsElliptic := TateCurve.isElliptic hqT0 hqT1
    haveI : CharZero (AlgebraicClosure ℚ_[p]) :=
      charZero_of_injective_algebraMap (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective
    have hpQ : ((p : ℕ) : AlgebraicClosure ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpK : ((p : ℕ) : K) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hcardQ := WeierstrassCurve.card_torsion_of_isAlgClosed
      (K := AlgebraicClosure ℚ_[p]) (TateCurve.curve qT) hpQ
    have hcardK := WeierstrassCurve.card_torsion_of_isAlgClosed (K := K) (TateCurve.curve qT) hpK
    haveI : Finite (Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄K).Point p) :=
      Nat.finite_of_card_ne_zero (by rw [hcardK]; exact pow_ne_zero 2 hp.ne_zero)
    exact hinj.bijective_of_nat_card_le (by rw [hcardQ, hcardK])
  let br₁ : Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p ≃+
            Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄K).Point p :=
    AddEquiv.ofBijective br₁Fwd hbij
  have hbr₁_val : ∀ X,
      (↑(br₁ X) : ((TateCurve.curve qT)⁄K).Point)
        = Point.map ι (↑X : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point) :=
    fun _ => rfl

  let br₂ : ((TateCurve.curve qT)⁄K).n_torsionGen p ≃+ (TateCurve.curve q_K).n_torsionGen p :=
    torsionByAddEquivOfEq hcurve_eq' p

  let tte_K : (Fin p × Fin p) ≃ (TateCurve.curve q_K).n_torsionGen p :=
    Equiv.ofBijective _ (torsionMap_bijective hq_K0 hq_K1 hp hp3 hζ_K ht_K)
  let tte_K_add : (Fin p × Fin p) ≃+ (TateCurve.curve q_K).n_torsionGen p :=
    { tte_K with
      map_add' := fun a b => Subtype.ext <| by
        show tateTorsionPoint q_K ζ_K t_K hq_K0 hq_K1 hp hζ_K ht_K ((a + b).1 : ℕ) ((a + b).2 : ℕ)
          = tateTorsionPoint q_K ζ_K t_K hq_K0 hq_K1 hp hζ_K ht_K (a.1 : ℕ) (a.2 : ℕ)
            + tateTorsionPoint q_K ζ_K t_K hq_K0 hq_K1 hp hζ_K ht_K (b.1 : ℕ) (b.2 : ℕ)
        rw [Prod.fst_add, Prod.snd_add, Fin.val_add, Fin.val_add]
        exact ttp_add_mod hq_K0 hq_K1 hp hp3 hζ_K ht_K a.1.isLt a.2.isLt b.1.isLt b.2.isLt }

  let zm : (ZMod p × ZMod p) ≃+ (Fin p × Fin p) :=
    { toFun := fun a => (⟨a.1.val, a.1.val_lt⟩, ⟨a.2.val, a.2.val_lt⟩)
      invFun := fun i => ((i.1 : ZMod p), (i.2 : ZMod p))
      left_inv := fun a => by ext <;> simp [ZMod.natCast_val, ZMod.cast_id']
      right_inv := fun i => by
        ext <;> simp only [ZMod.val_natCast_of_lt (Fin.isLt _)]
      map_add' := fun a b => by
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Fin.add_def, ZMod.val_add] }

  let φAdd : (ZMod p × ZMod p) ≃+
      Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p :=
    zm.trans (tte_K_add.trans (br₂.symm.trans br₁.symm))

  have hφ_char : ∀ (a b : ZMod p),
      (Point.map ι ↑(φAdd (a, b)) : ((TateCurve.curve qT)⁄K).Point)
        = hcurve_eq'.symm ▸
          (tateTorsionPoint q_K ζ_K t_K hq_K0 hq_K1 hp hζ_K ht_K a.val b.val
            : (TateCurve.curve q_K).toAffine.Point) := by
    intro a b
    have htte : (↑(tte_K_add (zm (a, b))) : (TateCurve.curve q_K).toAffine.Point)
        = tateTorsionPoint q_K ζ_K t_K hq_K0 hq_K1 hp hζ_K ht_K a.val b.val := rfl
    have h0 : br₁ (φAdd (a, b)) = br₂.symm (tte_K_add (zm (a, b))) := br₁.apply_symm_apply _
    have h1 : (↑(br₁ (φAdd (a, b))) : ((TateCurve.curve qT)⁄K).Point)
        = Point.map ι ↑(φAdd (a, b)) := hbr₁_val (φAdd (a, b))
    have h2 : (↑(br₂.symm (tte_K_add (zm (a, b)))) : ((TateCurve.curve qT)⁄K).toAffine.Point)
        = hcurve_eq'.symm ▸ (↑(tte_K_add (zm (a, b))) : (TateCurve.curve q_K).toAffine.Point) :=
      torsionByAddEquivOfEq_symm_apply_val hcurve_eq' p _
    rw [← h1, h0, h2, htte]
  refine ⟨φAdd.toEquiv, ?_, ?_⟩
  ·
    intro a b
    rw [show φAdd.toEquiv (a + b) = φAdd (a + b) from rfl, φAdd.map_add]
    exact Submodule.coe_add _ _
  ·
    intro σ e c hσζ hσt i j
    obtain ⟨σK, hσKiso, hext_σ⟩ := hext σ
    have hσKinj : Function.Injective σK := hσKiso.injective
    have hσKq : σK q_K = q_K := by
      rw [hq_K_def, ← ι.commutes qT, hext_σ,
        show σ (algebraMap ℚ_[p] _ qT) = algebraMap ℚ_[p] _ qT from σ.commutes qT]
    have hσKζ : σK ζ_K = ζ_K ^ e := by rw [hζ_K_def, hext_σ, hσζ, map_pow]
    have hσKt : σK t_K = ζ_K ^ c * t_K := by
      rw [ht_K_def, hext_σ, hσt, map_mul, map_pow]

    let σK_alg : K →ₐ[ℚ_[p]] K :=
      { toRingHom := σK
        commutes' := fun r => by
          show σK (algebraMap ℚ_[p] K r) = algebraMap ℚ_[p] K r
          rw [← ι.commutes r, hext_σ, σ.commutes r] }
    have hcomp : (ι : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] K).comp σ.toAlgHom = σK_alg.comp ι :=
      AlgHom.ext fun x => (hext_σ x).symm
    have hfunc : ∀ (P : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point),
        Point.map ι (Point.map σ.toAlgHom P) = Point.map σK_alg (Point.map ι P) := by
      intro P
      calc Point.map ι (Point.map σ.toAlgHom P)
          = Point.map ((ι : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] K).comp σ.toAlgHom) P := by
            cases P <;> rfl
        _ = Point.map (σK_alg.comp ι) P := by rw [hcomp]
        _ = Point.map σK_alg (Point.map ι P) := by cases P <;> rfl

    apply hbij.1
    apply Subtype.ext
    show Point.map ι ((σ • φAdd (i, j) :
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p)
        : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
        = Point.map ι ((φAdd (e • i + c • j, j) :
            Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p)
          : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
    have hsmul_val : ((σ • φAdd (i, j) :
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p)
        : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
        = Point.map σ.toAlgHom
            (φAdd (i, j) : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point) := rfl
    rw [hsmul_val, hfunc, hφ_char i j, hφ_char (e • i + c • j) j]
    have hnsmul_val : ∀ (n : ℕ) (x : ZMod p), (n • x).val = (n * x.val) % p := by
      intro n x
      induction n with
      | zero => simp [Nat.zero_mod]
      | succ m ih =>
        rw [succ_nsmul, ZMod.val_add, ih, Nat.succ_mul, Nat.mod_add_mod]
    have hval : (e • i + c • j).val = (e * i.val + c * j.val) % p := by
      rw [ZMod.val_add, hnsmul_val e i, hnsmul_val c j, Nat.add_mod_mod, Nat.mod_add_mod]
    rw [hval]
    by_cases hij0 : i.val = 0 ∧ j.val = 0
    · obtain ⟨hi0, hj0⟩ := hij0
      simp only [hi0, hj0, mul_zero, add_zero, Nat.zero_mod, tateTorsionPoint_zero_zero,
        transport_point_zero hcurve_eq', AddMonoidHom.map_zero]
    · have hi_lt : i.val < p := i.val_lt
      have hj_lt : j.val < p := j.val_lt
      set i₂ := (e * i.val + c * j.val) % p with hi₂def
      have hi₂ : i₂ < p := Nat.mod_lt _ hp.pos
      have hpe : ¬ p ∣ e := by
        intro hdvd
        obtain ⟨k, rfl⟩ := hdvd
        have h1 : ζ_K ^ (p * k) = 1 := by rw [pow_mul, hζ_K.pow_eq_one, one_pow]
        exact hζ_K.ne_one hp.one_lt (hσKinj ((hσKζ.trans h1).trans (map_one σK).symm))
      have hij₂ : ¬(i₂ = 0 ∧ j.val = 0) := by
        rintro ⟨h1, h2⟩
        refine hij0 ⟨?_, h2⟩
        rw [hi₂def, h2, mul_zero, add_zero] at h1
        rcases Nat.eq_zero_or_pos i.val with h0 | hpos
        · exact h0
        · exact absurd
            (Nat.le_of_dvd hpos
              ((Nat.Prime.dvd_mul hp).mp (Nat.dvd_of_mod_eq_zero h1) |>.resolve_left hpe))
            (by omega)
      rw [tateTorsionPoint_spec hq_K0 hq_K1 hp hζ_K ht_K hi_lt hj_lt hij0,
          transport_point_some hcurve_eq' _,
          tateTorsionPoint_spec hq_K0 hq_K1 hp hζ_K ht_K hi₂ hj_lt hij₂,
          transport_point_some hcurve_eq' _]
      have hX : σK (pointX q_K (ζ_K ^ i.val * t_K ^ j.val))
          = pointX q_K (ζ_K ^ i₂ * t_K ^ j.val) := by
        rw [map_pointX_tateParam hq_K0 hq_K1 hp hζ_K ht_K σK hσKiso hσKq hσKζ hσKt i.val j.val,
            hi₂def, zeta_pow_mod hζ_K.pow_eq_one (e * i.val + c * j.val)]
      have hY : σK (pointY q_K (ζ_K ^ i.val * t_K ^ j.val))
          = pointY q_K (ζ_K ^ i₂ * t_K ^ j.val) := by
        rw [map_pointY_tateParam hq_K0 hq_K1 hp hζ_K ht_K σK hσKiso hσKq hσKζ hσKt i.val j.val,
            hi₂def, zeta_pow_mod hζ_K.pow_eq_one (e * i.val + c * j.val)]
      have hns_target : ((TateCurve.curve qT)⁄K).toAffine.Nonsingular
          (σK (pointX q_K (ζ_K ^ i.val * t_K ^ j.val)))
          (σK (pointY q_K (ζ_K ^ i.val * t_K ^ j.val))) := by
        rw [hX, hY]
        exact transport_nonsingular hcurve_eq'
          (nonsingular_point hq_K0 hq_K1 (tateParam_ne_zero hζ_K0 ht_K0)
            (tateParam_offLattice hq_K0 hq_K1 hζ_K ht_K hi₂ hj_lt hij₂))
      calc (Point.map σK_alg (Point.some (pointX q_K (ζ_K ^ i.val * t_K ^ j.val))
              (pointY q_K (ζ_K ^ i.val * t_K ^ j.val)) _)
            : ((TateCurve.curve qT)⁄K).Point)
          = Point.some (σK (pointX q_K (ζ_K ^ i.val * t_K ^ j.val)))
              (σK (pointY q_K (ζ_K ^ i.val * t_K ^ j.val))) hns_target := rfl
        _ = Point.some (pointX q_K (ζ_K ^ i₂ * t_K ^ j.val))
              (pointY q_K (ζ_K ^ i₂ * t_K ^ j.val)) _ := point_some_congr hX hY hns_target _

end EqThree
end TateCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (hp3 : p = 3) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (ζ t : AlgebraicClosure ℚ_[p]), IsPrimitiveRoot ζ p ∧
      t ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) qT ∧
    ∃ φ : (ZMod p × ZMod p) ≃
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
      (∀ a b, (φ (a + b) : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
              = (φ a : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)
              + (φ b : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point)) ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (e c : ℕ),
        σ ζ = ζ ^ e → σ t = ζ ^ c * t →
        ∀ i j : ZMod p, σ • (φ (i, j)) = φ (e • i + c • j, j) :=
  TateCurve.EqThree.exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_eq_three p hp3 qT hqT0 hqT1

end S_TateCurve_exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_eq_three
end P2MW
export P2MW.S_TateCurve_exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_eq_three (solution)
