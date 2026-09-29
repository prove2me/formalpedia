-- Prove2me | solution 1 for TateCurve.point_mul_eq_add_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a8e1f2f3-1915-5a9e-ba62-688de7713b72

import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_point_mul_eq_add_of_norm_eq_one

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false

noncomputable section

open WeierstrassCurve.Affine Polynomial
open scoped NNReal

namespace TateCurve
p2m_export "TateCurve" "point_mul_eq_add_of_symAddHyps_of_diffHyp eq_or_mul_eq_one_of_pointX_eq two_nsmul_point_ne_zero SymAddHyps nonsingular_point OffLattice AddParams offLattice_of_norm_eq_one ne_zero_of_norm_eq_one pointX pointY b curve DiffHyp symAddHyps_unconditional diffHyp_unconditional"
p2m_open "TateCurve"

namespace P2MUnitCircle

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q : K}

theorem point_some_congr {W : WeierstrassCurve K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

theorem ne_zero_of_norm_eq_one {a : K} (ha : ‖a‖ = 1) : a ≠ 0 := by
  intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha

theorem norm_eq_one_of_pow_eq_one {s : K} {n : ℕ} (hn : n ≠ 0) (hs : s ^ n = 1) : ‖s‖ = 1 := by
  have h1 : ‖s‖ ^ n = 1 := by rw [← norm_pow, hs, norm_one]
  rcases (pow_eq_one_iff_of_ne_zero hn).mp h1 with h | ⟨h, _⟩
  · exact h
  · exfalso
    have h2 := norm_nonneg s
    rw [h] at h2
    linarith

theorem offLattice_of_norm_one (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {a : K} (ha : ‖a‖ = 1)
    (ha1 : a ≠ 1) : OffLattice q a :=
  offLattice_of_norm_eq_one hq0 (by exact_mod_cast hq) ha ha1

theorem nonsingular_of_norm_one (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {a : K} (ha : ‖a‖ = 1)
    (ha1 : a ≠ 1) : (curve q).toAffine.Nonsingular (pointX q a) (pointY q a) :=
  nonsingular_point hq0 hq (ne_zero_of_norm_eq_one ha) (offLattice_of_norm_one hq0 hq ha ha1)

theorem pointX_ne_of_norm_one (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {a b : K} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hab1 : a * b ≠ 1) :
    pointX q a ≠ pointX q b := by
  intro hX
  have hq1 : ‖q‖ < 1 := by exact_mod_cast hq
  rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq (ne_zero_of_norm_eq_one ha)
      (ne_zero_of_norm_eq_one hb) (offLattice_of_norm_one hq0 hq ha ha1)
      (offLattice_of_norm_one hq0 hq hb hb1) ha.le hb.le
      (by rw [norm_mul, ha, hb, one_mul]; exact hq1) hX with h | h
  · exact hab h
  · exact hab1 h

theorem point_mul_eq_add_generic [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {a b : K}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab1 : a * b ≠ 1)
    (hab : a ≠ b) (haab : a ^ 2 * b ≠ 1) (haa : a ^ 2 ≠ 1)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (a * b)) (pointY q (a * b)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q a) (pointY q a))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q b) (pointY q b)) :
    (Point.some (pointX q (a * b)) (pointY q (a * b)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q a) (pointY q a) h₂ + Point.some (pointX q b) (pointY q b) h₃ := by
  have hyps : SymAddHyps q := symAddHyps_unconditional hq0 hq
  have hdiff : DiffHyp q := diffHyp_unconditional hq0 (by exact_mod_cast hq)
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  have hb0 : b ≠ 0 := ne_zero_of_norm_eq_one hb
  have hnab : ‖a * b‖ = 1 := by rw [norm_mul, ha, hb, one_mul]
  have hnainv : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
  have hnabinv : ‖a * b⁻¹‖ = 1 := by rw [norm_mul, norm_inv, ha, hb, inv_one, one_mul]
  have hnaab : ‖a ^ 2 * b‖ = 1 := by rw [norm_mul, norm_pow, ha, hb, one_pow, one_mul]
  have hnaa : ‖a ^ 2‖ = 1 := by rw [norm_pow, ha, one_pow]
  have habinv1 : a * b⁻¹ ≠ 1 := by
    intro h
    apply hab
    have h2 : a * b⁻¹ * b = 1 * b := by rw [h]
    rwa [mul_assoc, inv_mul_cancel₀ hb0, mul_one, one_mul] at h2
  have hainv1 : a⁻¹ ≠ 1 := by
    intro h; apply ha1; rw [← inv_inv a, h, inv_one]

  have hp : AddParams q a b :=
    ⟨hq0, ha0, hb0, offLattice_of_norm_one hq0 hq ha ha1, offLattice_of_norm_one hq0 hq hb hb1,
      offLattice_of_norm_one hq0 hq hnab hab1, offLattice_of_norm_one hq0 hq hnabinv habinv1⟩
  have hxne : pointX q a ≠ pointX q b := pointX_ne_of_norm_one hq0 hq ha hb ha1 hb1 hab hab1

  have helem1 : a * b * a⁻¹ = b := by
    rw [mul_comm a b, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
  have helem2 : a * b * a⁻¹⁻¹ = a ^ 2 * b := by rw [inv_inv]; ring
  have hp' : AddParams q (a * b) a⁻¹ := by
    refine ⟨hq0, mul_ne_zero ha0 hb0, inv_ne_zero ha0, offLattice_of_norm_one hq0 hq hnab hab1,
      offLattice_of_norm_one hq0 hq hnainv hainv1, ?_, ?_⟩
    · rw [helem1]; exact offLattice_of_norm_one hq0 hq hb hb1
    · rw [helem2]; exact offLattice_of_norm_one hq0 hq hnaab haab
  have hxne' : pointX q (a * b) ≠ pointX q a := by
    refine pointX_ne_of_norm_one hq0 hq hnab ha hab1 ha1 ?_ ?_
    · intro h
      apply hb1
      have h2 : a⁻¹ * (a * b) = a⁻¹ * a := by rw [h]
      rwa [← mul_assoc, inv_mul_cancel₀ ha0, one_mul] at h2
    · rw [show a * b * a = a ^ 2 * b by ring]; exact haab

  have hP2 : (Point.some (pointX q a) (pointY q a) h₂ : (curve q).toAffine.Point)
      + Point.some (pointX q a) (pointY q a) h₂ ≠ 0 := by
    have h := two_nsmul_point_ne_zero hyps hq0 hq ha0 (offLattice_of_norm_one hq0 hq ha ha1)
      (offLattice_of_norm_one hq0 hq hnaa haa) h₂
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

theorem point_mul_eq_add_of_norm_eq_one' [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    {v w : K} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v * w ≠ 1)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (v * w)) (pointY q (v * w)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w)) :
    (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃ := by
  have hv0 : v ≠ 0 := ne_zero_of_norm_eq_one hv
  have hw0 : w ≠ 0 := ne_zero_of_norm_eq_one hw
  have hvw0 : v * w ≠ 0 := mul_ne_zero hv0 hw0
  have hv20 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv0
  have hv2w0 : v ^ 2 * w ≠ 0 := mul_ne_zero hv20 hw0

  obtain ⟨s, n, hn0, hsn, hs⟩ := exists_pow_eq_one_forall_ne
    [((1 : K), (1 : K), 1), (v, 1, 1), (1, v, 1), (v, 1, 2), (1, 1, 2), (v * w, 1, 1), (v, w, 1),
      (v ^ 2 * w, 1, 2), (v ^ 2, 1, 2), (1, v * w, 1), (v * w, 1, 2)]
    (by
      intro t ht
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [hv0, hw0])
  have c0 : (1 : K) * s ^ 1 ≠ 1 := hs ((1 : K), (1 : K), 1) (by simp)
  have c1 : v * s ^ 1 ≠ 1 := hs (v, 1, 1) (by simp)
  have c2 : (1 : K) * s ^ 1 ≠ v := hs (1, v, 1) (by simp)
  have c3 : v * s ^ 2 ≠ 1 := hs (v, 1, 2) (by simp)
  have c4 : (1 : K) * s ^ 2 ≠ 1 := hs (1, 1, 2) (by simp)
  have c5 : v * w * s ^ 1 ≠ 1 := hs (v * w, 1, 1) (by simp)
  have c6 : v * s ^ 1 ≠ w := hs (v, w, 1) (by simp)
  have c7 : v ^ 2 * w * s ^ 2 ≠ 1 := hs (v ^ 2 * w, 1, 2) (by simp)
  have c8 : v ^ 2 * s ^ 2 ≠ 1 := hs (v ^ 2, 1, 2) (by simp)
  have c9 : (1 : K) * s ^ 1 ≠ v * w := hs (1, v * w, 1) (by simp)
  have c10 : v * w * s ^ 2 ≠ 1 := hs (v * w, 1, 2) (by simp)
  simp only [one_mul, pow_one] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10

  have hs1 : ‖s‖ = 1 := norm_eq_one_of_pow_eq_one hn0 hsn
  have hsv : ‖s * v‖ = 1 := by rw [norm_mul, hs1, hv, one_mul]
  have hvwn : ‖v * w‖ = 1 := by rw [norm_mul, hv, hw, one_mul]
  have hsvw : ‖s * v * w‖ = 1 := by rw [norm_mul, hsv, hw, one_mul]

  have e_sv1 : s * v ≠ 1 := by rwa [mul_comm] at c1
  have e_s_v : s ≠ v := c2
  have e_ssv : s ^ 2 * v ≠ 1 := by rwa [mul_comm] at c3
  have e_svw1 : s * v * w ≠ 1 := by
    intro h; apply c5; rw [← h]; ring
  have e_svw1' : s * (v * w) ≠ 1 := by rw [← mul_assoc]; exact e_svw1
  have e_sv_w : s * v ≠ w := by rwa [mul_comm] at c6
  have e_svsvw : (s * v) ^ 2 * w ≠ 1 := by
    intro h; apply c7; rw [← h]; ring
  have e_svsv : (s * v) ^ 2 ≠ 1 := by
    intro h; apply c8; rw [← h]; ring
  have e_s_vw : s ≠ v * w := c9
  have e_ssvw : s ^ 2 * (v * w) ≠ 1 := by
    intro h; apply c10; rw [← h]; ring

  have hns_s := nonsingular_of_norm_one hq0 hq hs1 c0
  have hns_sv := nonsingular_of_norm_one hq0 hq hsv e_sv1
  have hns_svw := nonsingular_of_norm_one hq0 hq hsvw e_svw1
  have hns_svw' : (curve q).toAffine.Nonsingular (pointX q (s * (v * w)))
      (pointY q (s * (v * w))) := by
    rw [← mul_assoc]; exact hns_svw

  have A1 := point_mul_eq_add_generic hq0 hq hs1 hv c0 hv1 e_sv1 e_s_v e_ssv c4 hns_sv hns_s h₂
  have A2 := point_mul_eq_add_generic hq0 hq hsv hw e_sv1 hw1 e_svw1 e_sv_w e_svsvw e_svsv
    hns_svw hns_sv h₃
  have A3 := point_mul_eq_add_generic hq0 hq hs1 hvwn c0 hvw e_svw1' e_s_vw e_ssvw c4
    hns_svw' hns_s h₁

  have e13 : (Point.some (pointX q (s * v * w)) (pointY q (s * v * w)) hns_svw :
      (curve q).toAffine.Point)
      = Point.some (pointX q (s * (v * w))) (pointY q (s * (v * w))) hns_svw' :=
    point_some_congr (by rw [mul_assoc]) (by rw [mul_assoc]) _ _
  have key : (Point.some (pointX q s) (pointY q s) hns_s : (curve q).toAffine.Point)
      + Point.some (pointX q (v * w)) (pointY q (v * w)) h₁
      = Point.some (pointX q s) (pointY q s) hns_s
        + (Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃) := by
    rw [← A3, ← e13, A2, A1, add_assoc]
  exact add_left_cancel key

end P2MUnitCircle

end TateCurve

end

p2m_open "TateCurve P2MW.S_TateCurve_point_mul_eq_add_of_norm_eq_one.TateCurve WeierstrassCurve.Affine"
open scoped NNReal

universe u in
theorem solution
    {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K]
    {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {v w : K} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v * w ≠ 1)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (v * w)) (pointY q (v * w)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w)) :
    (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃ :=
  TateCurve.P2MUnitCircle.point_mul_eq_add_of_norm_eq_one' hq0 hq hv hw hv1 hw1 hvw h₁ h₂ h₃

end S_TateCurve_point_mul_eq_add_of_norm_eq_one
end P2MW
export P2MW.S_TateCurve_point_mul_eq_add_of_norm_eq_one (solution)
