-- Prove2me | solution 1 for TateCurve.point_mul_eq_add_of_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e3c67fc8-0622-5569-907c-9475fb1777b1

import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_point_mul_eq_add_of_norm_le_one

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false

noncomputable section

open WeierstrassCurve.Affine Polynomial
open scoped NNReal

namespace TateCurve
p2m_export "TateCurve" "point_mul_eq_add_of_symAddHyps_of_diffHyp eq_or_mul_eq_one_of_pointX_eq two_nsmul_point_ne_zero SymAddHyps nonsingular_point OffLattice OffLattice.q_mul OffLattice.inv AddParams offLattice_of_norm_eq_one pointX pointY b curve pointX_inv pointX_q_mul DiffHyp symAddHyps_unconditional diffHyp_unconditional"
p2m_open "TateCurve"

namespace P2MAnnulus

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q : K}

theorem point_some_congr {W : WeierstrassCurve K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

theorem ne_zero_of_norm_lt {a : K} (h : ‖q‖ < ‖a‖) : a ≠ 0 := by
  intro h0; rw [h0, norm_zero] at h; exact (not_lt.mpr (norm_nonneg q)) h

theorem norm_eq_one_of_pow_eq_one {s : K} {n : ℕ} (hn : n ≠ 0) (hs : s ^ n = 1) : ‖s‖ = 1 := by
  have h1 : ‖s‖ ^ n = 1 := by rw [← norm_pow, hs, norm_one]
  rcases (pow_eq_one_iff_of_ne_zero hn).mp h1 with h | ⟨h, _⟩
  · exact h
  · exfalso
    have h2 := norm_nonneg s
    rw [h] at h2
    linarith

theorem offLattice_of_window (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {a : K} {A B : ℤ}
    (hA : ‖q‖ ^ A < ‖a‖) (hB : ‖a‖ ≤ ‖q‖ ^ B)
    (hne : ∀ m : ℤ, B ≤ m → m < A → a ≠ q ^ m) : OffLattice q a := by
  intro n hn
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have ha : a = q ^ (-n) := by
    rw [zpow_neg]; exact eq_inv_of_mul_eq_one_right hn
  have hnorm : ‖a‖ = ‖q‖ ^ (-n) := by rw [ha, norm_zpow]
  have h1 : -n < A := by
    by_contra h
    push Not at h
    have h2 : ‖q‖ ^ (-n) ≤ ‖q‖ ^ A := zpow_le_zpow_right_of_le_one₀ hqpos hq.le h
    rw [← hnorm] at h2
    exact absurd (lt_of_lt_of_le hA h2) (lt_irrefl _)
  have h2 : B ≤ -n := by
    by_contra h
    push Not at h
    have h3 : ‖q‖ ^ B < ‖q‖ ^ (-n) := zpow_lt_zpow_right_of_lt_one₀ hqpos hq h
    rw [← hnorm] at h3
    exact absurd (lt_of_le_of_lt hB h3) (lt_irrefl _)
  exact hne (-n) h2 h1 ha

theorem offLattice_of_annulus (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {a : K}
    (hqa : ‖q‖ < ‖a‖) (ha1 : ‖a‖ ≤ 1) (ha : a ≠ 1) : OffLattice q a := by
  refine offLattice_of_window hq0 hq (A := 1) (B := 0) (by rwa [zpow_one]) (by rwa [zpow_zero]) ?_
  intro m h0 h1 h
  have hm : m = 0 := by omega
  rw [hm, zpow_zero] at h
  exact ha h

theorem offLattice_of_annulus_sq (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {a : K}
    (hqa : ‖q‖ ^ 2 < ‖a‖) (ha1 : ‖a‖ ≤ 1) (ha : a ≠ 1) (haq : a ≠ q) : OffLattice q a := by
  refine offLattice_of_window hq0 hq (A := 2) (B := 0) (by exact_mod_cast hqa)
    (by rwa [zpow_zero]) ?_
  intro m h0 h1 h
  rcases (show m = 0 ∨ m = 1 by omega) with hm | hm
  · rw [hm, zpow_zero] at h; exact ha h
  · rw [hm, zpow_one] at h; exact haq h

theorem offLattice_of_one_le (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {a : K}
    (ha1 : 1 ≤ ‖a‖) (hqa : ‖a‖ < ‖q‖⁻¹) (ha : a ≠ 1) (haq : a ≠ q⁻¹) : OffLattice q a := by
  refine offLattice_of_window hq0 hq (A := 1) (B := -1)
    (by rw [zpow_one]; exact lt_of_lt_of_le hq ha1) (by rw [zpow_neg, zpow_one]; exact hqa.le) ?_
  intro m h0 h1 h
  rcases (show m = 0 ∨ m = -1 by omega) with hm | hm
  · rw [hm, zpow_zero] at h; exact ha h
  · rw [hm, zpow_neg, zpow_one] at h; exact haq h

theorem nonsingular_of_annulus (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {a : K} (hqa : ‖q‖ < ‖a‖)
    (ha1 : ‖a‖ ≤ 1) (ha : a ≠ 1) : (curve q).toAffine.Nonsingular (pointX q a) (pointY q a) :=
  nonsingular_point hq0 hq (ne_zero_of_norm_lt hqa)
    (offLattice_of_annulus hq0 (by exact_mod_cast hq) hqa ha1 ha)

theorem eq_or_of_pointX_eq (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {a b : K}
    (hqa : ‖q‖ < ‖a‖) (ha1 : ‖a‖ ≤ 1) (hqb : ‖q‖ < ‖b‖) (hb1 : ‖b‖ ≤ 1)
    (ha : OffLattice q a) (hb : OffLattice q b) (hside : ‖q‖ < ‖a * b‖ ∨ ‖a‖ ≠ ‖b‖)
    (hX : pointX q a = pointX q b) : a = b ∨ a * b = 1 ∨ a * b = q := by
  have hq1 : ‖q‖ < 1 := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have ha0 : a ≠ 0 := ne_zero_of_norm_lt hqa
  have hb0 : b ≠ 0 := ne_zero_of_norm_lt hqb
  have hapos : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha0
  have hbpos : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb0
  rcases hside with hside | hside
  · rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq ha0 hb0 ha hb ha1 hb1 hside hX with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases lt_or_gt_of_ne hside with hlt | hlt
    ·
      set a' : K := q * a⁻¹ with ha'
      have ha'0 : a' ≠ 0 := mul_ne_zero hq0 (inv_ne_zero ha0)
      have ha'off : OffLattice q a' := OffLattice.q_mul hq0 (OffLattice.inv hq0 ha)
      have hna' : ‖a'‖ = ‖q‖ * ‖a‖⁻¹ := by rw [ha', norm_mul, norm_inv]
      have ha'1 : ‖a'‖ ≤ 1 := by
        rw [hna', ← div_eq_mul_inv, div_le_one hapos]; exact hqa.le
      have hside' : ‖q‖ < ‖a' * b‖ := by
        rw [norm_mul, hna', mul_assoc, lt_mul_iff_one_lt_right hqpos, ← div_eq_inv_mul,
          one_lt_div hapos]
        exact hlt
      have hX' : pointX q a' = pointX q b := by
        rw [ha', pointX_q_mul hq0, pointX_inv hq0 ha0 ha]; exact hX
      rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq ha'0 hb0 ha'off hb ha'1 hb1 hside' hX' with h | h
      ·
        right; right
        rw [← h, ha']
        rw [mul_comm q a⁻¹, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
      ·
        exfalso
        have hb' : b = a * q⁻¹ := by
          have h2 : a * q⁻¹ * (q * a⁻¹ * b) = a * q⁻¹ * 1 := by rw [← ha', h]
          rw [mul_one] at h2
          rw [← h2]; field_simp
        have hnb : ‖b‖ = ‖a‖ * ‖q‖⁻¹ := by rw [hb', norm_mul, norm_inv]
        have h3 : 1 < ‖a‖ * ‖q‖⁻¹ := by
          rw [← div_eq_mul_inv, one_lt_div hqpos]; exact hqa
        rw [← hnb] at h3
        exact absurd (lt_of_lt_of_le h3 hb1) (lt_irrefl _)
    ·
      set b' : K := q * b⁻¹ with hb'
      have hb'0 : b' ≠ 0 := mul_ne_zero hq0 (inv_ne_zero hb0)
      have hb'off : OffLattice q b' := OffLattice.q_mul hq0 (OffLattice.inv hq0 hb)
      have hnb' : ‖b'‖ = ‖q‖ * ‖b‖⁻¹ := by rw [hb', norm_mul, norm_inv]
      have hb'1 : ‖b'‖ ≤ 1 := by
        rw [hnb', ← div_eq_mul_inv, div_le_one hbpos]; exact hqb.le
      have hside' : ‖q‖ < ‖a * b'‖ := by
        rw [norm_mul, hnb', mul_comm ‖a‖, mul_assoc, lt_mul_iff_one_lt_right hqpos,
          ← div_eq_inv_mul, one_lt_div hbpos]
        exact hlt
      have hX' : pointX q a = pointX q b' := by
        rw [hb', pointX_q_mul hq0, pointX_inv hq0 hb0 hb]; exact hX
      rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq ha0 hb'0 ha hb'off ha1 hb'1 hside' hX' with h | h
      ·
        right; right
        rw [h, hb', mul_assoc, inv_mul_cancel₀ hb0, mul_one]
      ·
        exfalso
        have hbb : b = a * q := by
          have h2 : a * (q * b⁻¹) * b = 1 * b := by rw [← hb', h]
          rw [mul_assoc, mul_assoc, inv_mul_cancel₀ hb0, mul_one, one_mul] at h2
          exact h2.symm
        have hnb : ‖b‖ ≤ ‖q‖ := by
          rw [hbb, norm_mul]
          calc ‖a‖ * ‖q‖ ≤ 1 * ‖q‖ := mul_le_mul_of_nonneg_right ha1 hqpos.le
            _ = ‖q‖ := one_mul _
        exact absurd (lt_of_lt_of_le hqb hnb) (lt_irrefl _)

theorem point_mul_eq_add_generic [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {a b : K}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : OffLattice q a) (hb : OffLattice q b)
    (hab : OffLattice q (a * b)) (habi : OffLattice q (a * b⁻¹)) (haab : OffLattice q (a ^ 2 * b))
    (haa : OffLattice q (a ^ 2)) (hxne : pointX q a ≠ pointX q b)
    (hxne' : pointX q (a * b) ≠ pointX q a)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (a * b)) (pointY q (a * b)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q a) (pointY q a))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q b) (pointY q b)) :
    (Point.some (pointX q (a * b)) (pointY q (a * b)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q a) (pointY q a) h₂ + Point.some (pointX q b) (pointY q b) h₃ := by
  have hyps : SymAddHyps q := symAddHyps_unconditional hq0 hq
  have hdiff : DiffHyp q := diffHyp_unconditional hq0 (by exact_mod_cast hq)
  have hp : AddParams q a b := ⟨hq0, ha0, hb0, ha, hb, hab, habi⟩
  have helem1 : a * b * a⁻¹ = b := by
    rw [mul_comm a b, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
  have helem2 : a * b * a⁻¹⁻¹ = a ^ 2 * b := by rw [inv_inv]; ring
  have hp' : AddParams q (a * b) a⁻¹ := by
    refine ⟨hq0, mul_ne_zero ha0 hb0, inv_ne_zero ha0, hab, OffLattice.inv hq0 ha, ?_, ?_⟩
    · rw [helem1]; exact hb
    · rw [helem2]; exact haab
  have hP2 : (Point.some (pointX q a) (pointY q a) h₂ : (curve q).toAffine.Point)
      + Point.some (pointX q a) (pointY q a) h₂ ≠ 0 := by
    have h := two_nsmul_point_ne_zero hyps hq0 hq ha0 ha haa h₂
    rwa [two_nsmul] at h
  exact point_mul_eq_add_of_symAddHyps_of_diffHyp hyps hdiff hq0 hq hp hxne hp' hxne' h₁ h₂ h₃ hP2

theorem exists_pow_eq_one_forall_ne {L : Type*} [Field L] [IsAlgClosed L] [CharZero L]
    (l : List (L × L × ℕ)) (hl : ∀ t ∈ l, t.1 ≠ 0 ∧ t.2.2 ≠ 0) :
    ∃ s : L, ∃ n : ℕ, n ≠ 0 ∧ s ^ n = 1 ∧ ∀ t ∈ l, t.1 * s ^ t.2.2 ≠ t.2.1 := by
  classical
  let P : L[X] := (l.map fun t => C t.1 * X ^ t.2.2 - C t.2.1).prod
  have hfac : ∀ t ∈ l, (C t.1 * X ^ t.2.2 - C t.2.1 : L[X]) ≠ 0 := by
    intro t ht h
    have h2 := congrArg (fun p : L[X] => p.coeff t.2.2) h
    simp only [coeff_sub, coeff_C_mul, coeff_X_pow, if_true, mul_one, coeff_C, (hl t ht).2,
      if_false, sub_zero, coeff_zero] at h2
    exact (hl t ht).1 h2
  have hP : P ≠ 0 := by
    refine List.prod_ne_zero fun h0 => ?_
    obtain ⟨t, ht, ht0⟩ := List.mem_map.mp h0
    exact hfac t ht ht0
  let B : Finset L := P.roots.toFinset
  set n : ℕ := B.card + 1 with hn
  have hn0 : n ≠ 0 := Nat.succ_ne_zero _
  haveI : NeZero (n : L) := NeZero.charZero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L n
  have hcard : B.card < (Polynomial.nthRootsFinset n (1 : L)).card := by
    rw [hζ.card_nthRootsFinset]; omega
  obtain ⟨s, hs, hsB⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn0)] at hs
  refine ⟨s, n, hn0, hs, fun t ht h => hsB ?_⟩
  rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_list_prod, List.prod_eq_zero_iff,
    List.map_map, List.mem_map]
  refine ⟨t, ht, ?_⟩
  simp only [Function.comp_apply, eval_sub, eval_mul, eval_C, eval_pow, eval_X, h, sub_self]

theorem main_of_le [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    {v w : K} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hqvw : ‖q‖ < ‖v * w‖) (hwv : ‖w‖ ≤ ‖v‖)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v * w ≠ 1)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (v * w)) (pointY q (v * w)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w)) :
    (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃ := by
  have hq1 : ‖q‖ < 1 := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0

  set u : K := v * w with hu
  have hnu : ‖u‖ = ‖v‖ * ‖w‖ := norm_mul v w
  have hnu1 : ‖u‖ ≤ 1 := by rw [hnu]; exact mul_le_one₀ hv (norm_nonneg w) hw
  have hqv : ‖q‖ < ‖v‖ := lt_of_lt_of_le hqvw (by rw [hnu]; exact mul_le_of_le_one_right (norm_nonneg v) hw)
  have hqw : ‖q‖ < ‖w‖ := lt_of_lt_of_le hqvw (by rw [hnu]; exact mul_le_of_le_one_left (norm_nonneg w) hv)
  have hv0 : v ≠ 0 := ne_zero_of_norm_lt hqv
  have hw0 : w ≠ 0 := ne_zero_of_norm_lt hqw
  have hu0 : u ≠ 0 := mul_ne_zero hv0 hw0
  have hvpos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
  have hv20 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv0
  have hv2w0 : v ^ 2 * w ≠ 0 := mul_ne_zero hv20 hw0
  have hvwi0 : v * w⁻¹ ≠ 0 := mul_ne_zero hv0 (inv_ne_zero hw0)

  obtain ⟨s, n, hn0, hsn, hs⟩ := exists_pow_eq_one_forall_ne
    [((1 : K), (1 : K), 1), (v, 1, 1), (1, v, 1), (v, 1, 2), (1, 1, 2), (u, 1, 1), (1, u, 1),
      (u, 1, 2), (v * w⁻¹, q⁻¹, 1), (v * w⁻¹, 1, 1), (v, w, 1), (v ^ 2 * w, 1, 2),
      (v ^ 2 * w, q, 2), (v ^ 2, 1, 2), (v ^ 2, q, 2)]
    (by
      intro t ht
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;>
        simp [hv0, hw0, hu0])
  have c1 : (1 : K) * s ^ 1 ≠ 1 := hs ((1 : K), (1 : K), 1) (by simp)
  have c2 : v * s ^ 1 ≠ 1 := hs (v, 1, 1) (by simp)
  have c3 : (1 : K) * s ^ 1 ≠ v := hs (1, v, 1) (by simp)
  have c5 : v * s ^ 2 ≠ 1 := hs (v, 1, 2) (by simp)
  have c6 : (1 : K) * s ^ 2 ≠ 1 := hs (1, 1, 2) (by simp)
  have c7 : u * s ^ 1 ≠ 1 := hs (u, 1, 1) (by simp)
  have c8 : (1 : K) * s ^ 1 ≠ u := hs (1, u, 1) (by simp)
  have c9 : u * s ^ 2 ≠ 1 := hs (u, 1, 2) (by simp)
  have c10 : v * w⁻¹ * s ^ 1 ≠ q⁻¹ := hs (v * w⁻¹, q⁻¹, 1) (by simp)
  have c11 : v * w⁻¹ * s ^ 1 ≠ 1 := hs (v * w⁻¹, 1, 1) (by simp)
  have c12 : v * s ^ 1 ≠ w := hs (v, w, 1) (by simp)
  have c13 : v ^ 2 * w * s ^ 2 ≠ 1 := hs (v ^ 2 * w, 1, 2) (by simp)
  have c14 : v ^ 2 * w * s ^ 2 ≠ q := hs (v ^ 2 * w, q, 2) (by simp)
  have c15 : v ^ 2 * s ^ 2 ≠ 1 := hs (v ^ 2, 1, 2) (by simp)
  have c16 : v ^ 2 * s ^ 2 ≠ q := hs (v ^ 2, q, 2) (by simp)
  simp only [one_mul, pow_one] at c1 c2 c3 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16

  have hs1 : ‖s‖ = 1 := norm_eq_one_of_pow_eq_one hn0 hsn
  have hs0 : s ≠ 0 := by intro h; rw [h, norm_zero] at hs1; exact zero_ne_one hs1
  have hns : ∀ x : K, ‖s * x‖ = ‖x‖ := fun x => by rw [norm_mul, hs1, one_mul]
  have hnss : ∀ x : K, ‖s ^ 2 * x‖ = ‖x‖ := fun x => by rw [norm_mul, norm_pow, hs1, one_pow, one_mul]

  have P_s : OffLattice q s := offLattice_of_norm_eq_one hq0 hq1 hs1 c1
  have P_ss : OffLattice q (s ^ 2) :=
    offLattice_of_norm_eq_one hq0 hq1 (by rw [norm_pow, hs1, one_pow]) c6
  have P_v : OffLattice q v := offLattice_of_annulus hq0 hq1 hqv hv hv1
  have P_w : OffLattice q w := offLattice_of_annulus hq0 hq1 hqw hw hw1
  have P_u : OffLattice q u := offLattice_of_annulus hq0 hq1 hqvw hnu1 hvw
  have P_sv : OffLattice q (s * v) :=
    offLattice_of_annulus hq0 hq1 (by rw [hns]; exact hqv) (by rw [hns]; exact hv)
      (by rwa [mul_comm] at c2)
  have P_su : OffLattice q (s * u) :=
    offLattice_of_annulus hq0 hq1 (by rw [hns]; exact hqvw) (by rw [hns]; exact hnu1)
      (by rwa [mul_comm] at c7)
  have P_siv : OffLattice q (s⁻¹ * v) := by
    refine offLattice_of_annulus hq0 hq1 (by rw [norm_mul, norm_inv, hs1, inv_one, one_mul]; exact hqv)
      (by rw [norm_mul, norm_inv, hs1, inv_one, one_mul]; exact hv) ?_
    intro h; apply c3
    have h2 : s * (s⁻¹ * v) = s * 1 := by rw [h]
    rw [← mul_assoc, mul_inv_cancel₀ hs0, one_mul, mul_one] at h2
    exact h2.symm
  have P_siu : OffLattice q (s⁻¹ * u) := by
    refine offLattice_of_annulus hq0 hq1 (by rw [norm_mul, norm_inv, hs1, inv_one, one_mul]; exact hqvw)
      (by rw [norm_mul, norm_inv, hs1, inv_one, one_mul]; exact hnu1) ?_
    intro h; apply c8
    have h2 : s * (s⁻¹ * u) = s * 1 := by rw [h]
    rw [← mul_assoc, mul_inv_cancel₀ hs0, one_mul, mul_one] at h2
    exact h2.symm
  have P_svi : OffLattice q (s * v⁻¹) := by
    have h := OffLattice.inv hq0 P_siv
    rwa [mul_inv_rev, inv_inv, mul_comm] at h
  have P_sui : OffLattice q (s * u⁻¹) := by
    have h := OffLattice.inv hq0 P_siu
    rwa [mul_inv_rev, inv_inv, mul_comm] at h
  have P_ssv : OffLattice q (s ^ 2 * v) :=
    offLattice_of_annulus hq0 hq1 (by rw [hnss]; exact hqv) (by rw [hnss]; exact hv)
      (by rwa [mul_comm] at c5)
  have P_ssu : OffLattice q (s ^ 2 * u) :=
    offLattice_of_annulus hq0 hq1 (by rw [hnss]; exact hqvw) (by rw [hnss]; exact hnu1)
      (by rwa [mul_comm] at c9)
  have P_svwi : OffLattice q (s * v * w⁻¹) := by
    have hnorm : ‖s * v * w⁻¹‖ = ‖v‖ * ‖w‖⁻¹ := by rw [norm_mul, hns, norm_inv]
    refine offLattice_of_one_le hq0 hq1 ?_ ?_ ?_ ?_
    · rw [hnorm, ← div_eq_mul_inv, one_le_div hwpos]; exact hwv
    · rw [hnorm]
      calc ‖v‖ * ‖w‖⁻¹ ≤ 1 * ‖w‖⁻¹ := mul_le_mul_of_nonneg_right hv (inv_nonneg.mpr (norm_nonneg w))
        _ = ‖w‖⁻¹ := one_mul _
        _ < ‖q‖⁻¹ := (inv_lt_inv₀ hwpos hqpos).mpr hqw
    · intro h; apply c11; rw [← h]; ring
    · intro h; apply c10; rw [← h]; ring
  have hqsq_v2w : ‖q‖ ^ 2 < ‖v ^ 2 * w‖ := by
    have h : ‖v ^ 2 * w‖ = ‖v‖ * ‖u‖ := by rw [hu, norm_mul, norm_mul, norm_pow, sq, mul_assoc]
    rw [h, sq]
    exact mul_lt_mul'' hqv hqvw hqpos.le hqpos.le
  have hv2w1 : ‖v ^ 2 * w‖ ≤ 1 := by
    rw [norm_mul, norm_pow]; exact mul_le_one₀ (pow_le_one₀ (norm_nonneg v) hv) (norm_nonneg w) hw
  have P_ssvvw : OffLattice q (s ^ 2 * (v ^ 2 * w)) :=
    offLattice_of_annulus_sq hq0 hq1 (by rw [hnss]; exact hqsq_v2w) (by rw [hnss]; exact hv2w1)
      (by intro h; apply c13; rw [← h]; ring) (by intro h; apply c14; rw [← h]; ring)
  have hqsq_v2 : ‖q‖ ^ 2 < ‖v ^ 2‖ := by
    rw [norm_pow]; exact pow_lt_pow_left₀ hqv hqpos.le two_ne_zero
  have hv21 : ‖v ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg v) hv
  have P_ssvv : OffLattice q (s ^ 2 * v ^ 2) :=
    offLattice_of_annulus_sq hq0 hq1 (by rw [hnss]; exact hqsq_v2) (by rw [hnss]; exact hv21)
      (by intro h; apply c15; rw [← h]; ring) (by intro h; apply c16; rw [← h]; ring)

  have hns_s : (curve q).toAffine.Nonsingular (pointX q s) (pointY q s) :=
    nonsingular_point hq0 hq hs0 P_s
  have hns_sv : (curve q).toAffine.Nonsingular (pointX q (s * v)) (pointY q (s * v)) :=
    nonsingular_point hq0 hq (mul_ne_zero hs0 hv0) P_sv
  have hns_su : (curve q).toAffine.Nonsingular (pointX q (s * u)) (pointY q (s * u)) :=
    nonsingular_point hq0 hq (mul_ne_zero hs0 hu0) P_su
  have hns_svw : (curve q).toAffine.Nonsingular (pointX q (s * v * w)) (pointY q (s * v * w)) := by
    rw [mul_assoc]; exact hns_su

  have X_s_v : pointX q s ≠ pointX q v := by
    intro hX
    rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hs0 hv0 P_s P_v hs1.le hv
      (by rw [hns]; exact hqv) hX with h | h
    · exact c3 h
    · exact c2 (by rwa [mul_comm] at h)
  have X_s_u : pointX q s ≠ pointX q u := by
    intro hX
    rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hs0 hu0 P_s P_u hs1.le hnu1
      (by rw [hns]; exact hqvw) hX with h | h
    · exact c8 h
    · exact c7 (by rwa [mul_comm] at h)
  have X_sv_s : pointX q (s * v) ≠ pointX q s := by
    intro hX
    rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq (mul_ne_zero hs0 hv0) hs0 P_sv P_s
      (by rw [hns]; exact hv) hs1.le (by rw [mul_comm, hns, hns]; exact hqv) hX with h | h
    · apply hv1
      have h2 : s⁻¹ * (s * v) = s⁻¹ * s := by rw [h]
      rwa [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] at h2
    · apply c5; rw [← h]; ring
  have X_su_s : pointX q (s * u) ≠ pointX q s := by
    intro hX
    rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq (mul_ne_zero hs0 hu0) hs0 P_su P_s
      (by rw [hns]; exact hnu1) hs1.le (by rw [mul_comm, hns, hns]; exact hqvw) hX with h | h
    · apply hvw
      have h2 : s⁻¹ * (s * u) = s⁻¹ * s := by rw [h]
      rwa [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] at h2
    · apply c9; rw [← h]; ring
  have X_sv_w : pointX q (s * v) ≠ pointX q w := by
    intro hX
    rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq (mul_ne_zero hs0 hv0) hw0 P_sv P_w
      (by rw [hns]; exact hv) hw (by rw [mul_assoc, hns]; exact hqvw) hX with h | h
    · exact c12 (by rwa [mul_comm] at h)
    · apply c7; rw [← h, hu]; ring
  have X_svw_sv : pointX q (s * v * w) ≠ pointX q (s * v) := by
    intro hX
    have hside : ‖q‖ < ‖s * v * w * (s * v)‖ ∨ ‖s * v * w‖ ≠ ‖s * v‖ := by
      by_cases hw1' : ‖w‖ = 1
      · left
        have hv1' : ‖v‖ = 1 := le_antisymm hv (hw1' ▸ hwv)
        simp only [norm_mul, hs1, hv1', hw1', one_mul]; exact hq1
      · right
        simp only [norm_mul, hs1, one_mul]
        intro h
        apply hw1'
        have h2 : ‖v‖ * ‖w‖ = ‖v‖ * 1 := by rw [h, mul_one]
        exact mul_left_cancel₀ hvpos.ne' h2
    rcases eq_or_of_pointX_eq hq0 hq (by rw [mul_assoc, hns]; exact hqvw)
      (by rw [mul_assoc, hns]; exact hnu1) (by rw [hns]; exact hqv) (by rw [hns]; exact hv)
      (by rw [mul_assoc]; exact P_su) P_sv hside hX with h | h | h
    · apply hw1
      have h2 : (s * v)⁻¹ * (s * v * w) = (s * v)⁻¹ * (s * v) := by rw [h]
      rwa [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hs0 hv0), one_mul] at h2
    · apply c13; rw [← h]; ring
    · apply c14; rw [← h]; ring

  have A1 := point_mul_eq_add_generic hq0 hq hs0 hv0 P_s P_v P_sv P_svi P_ssv P_ss X_s_v X_sv_s
    hns_sv hns_s h₂
  have A3 := point_mul_eq_add_generic hq0 hq hs0 hu0 P_s P_u P_su P_sui P_ssu P_ss X_s_u X_su_s
    hns_su hns_s h₁
  have A2 := point_mul_eq_add_generic hq0 hq (mul_ne_zero hs0 hv0) hw0 P_sv P_w
    (by rw [mul_assoc]; exact P_su) P_svwi
    (by rw [show (s * v) ^ 2 * w = s ^ 2 * (v ^ 2 * w) by ring]; exact P_ssvvw)
    (by rw [show (s * v) ^ 2 = s ^ 2 * v ^ 2 by ring]; exact P_ssvv) X_sv_w X_svw_sv
    hns_svw hns_sv h₃

  have e13 : (Point.some (pointX q (s * v * w)) (pointY q (s * v * w)) hns_svw :
      (curve q).toAffine.Point)
      = Point.some (pointX q (s * u)) (pointY q (s * u)) hns_su :=
    point_some_congr (by rw [mul_assoc]) (by rw [mul_assoc]) _ _
  have key : (Point.some (pointX q s) (pointY q s) hns_s : (curve q).toAffine.Point)
      + Point.some (pointX q u) (pointY q u) h₁
      = Point.some (pointX q s) (pointY q s) hns_s
        + (Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃) := by
    rw [← A3, ← e13, A2, A1, add_assoc]
  exact add_left_cancel key

theorem point_mul_eq_add_of_norm_le_one' [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    {v w : K} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hqvw : ‖q‖ < ‖v * w‖)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v * w ≠ 1)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (v * w)) (pointY q (v * w)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w)) :
    (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃ := by
  rcases le_total ‖w‖ ‖v‖ with hle | hle
  · exact main_of_le hq0 hq hv hw hqvw hle hv1 hw1 hvw h₁ h₂ h₃
  · have hqwv : ‖q‖ < ‖w * v‖ := by rwa [mul_comm]
    have hwv : w * v ≠ 1 := by rwa [mul_comm]
    have h₁' : (curve q).toAffine.Nonsingular (pointX q (w * v)) (pointY q (w * v)) := by
      rw [mul_comm]; exact h₁
    have h := main_of_le hq0 hq hw hv hqwv hle hw1 hv1 hwv h₁' h₃ h₂
    rw [add_comm] at h
    rw [← h]
    exact point_some_congr (by rw [mul_comm]) (by rw [mul_comm]) _ _

end P2MAnnulus

end TateCurve

end

p2m_open "TateCurve P2MW.S_TateCurve_point_mul_eq_add_of_norm_le_one.TateCurve WeierstrassCurve.Affine"
open scoped NNReal

universe u in
theorem solution
    {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K]
    {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {v w : K} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hqvw : ‖q‖ < ‖v * w‖) (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v * w ≠ 1)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (v * w)) (pointY q (v * w)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w)) :
    (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃ :=
  TateCurve.P2MAnnulus.point_mul_eq_add_of_norm_le_one' hq0 hq hv hw hqvw hv1 hw1 hvw h₁ h₂ h₃

end S_TateCurve_point_mul_eq_add_of_norm_le_one
end P2MW
export P2MW.S_TateCurve_point_mul_eq_add_of_norm_le_one (solution)
