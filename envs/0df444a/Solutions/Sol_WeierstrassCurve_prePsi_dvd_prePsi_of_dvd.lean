-- Prove2me | solution 1 for WeierstrassCurve.prePsi_dvd_prePsi_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1e6a8d36-9b66-58e4-98b2-2443ae783a95

import Mathlib
import Theorems.Thm_isEllSequence_normEDS
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_prePsi_dvd_prePsi_of_dvd
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
universe u
open Polynomial

namespace PsiDvdProof

theorem normEDS_two_three_two_nat (n : ℕ) : normEDS (2 : ℤ) 3 2 n = n := by
  induction n using normEDSRec' with
  | zero => simp
  | one => simp
  | two => simp
  | three => simp
  | four => simp
  | even m ih =>
    have e1 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 1) = (m : ℤ) + 1 := by
      have := ih (m + 1) (by omega); push_cast at this; exact this
    have e2 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 2) = (m : ℤ) + 2 := by
      have := ih (m + 2) (by omega); push_cast at this; exact this
    have e3 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 3) = (m : ℤ) + 3 := by
      have := ih (m + 3) (by omega); push_cast at this; exact this
    have e4 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 4) = (m : ℤ) + 4 := by
      have := ih (m + 4) (by omega); push_cast at this; exact this
    have e5 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 5) = (m : ℤ) + 5 := by
      have := ih (m + 5) (by omega); push_cast at this; exact this
    have h := normEDS_even (2 : ℤ) 3 2 ((m : ℤ) + 3)
    rw [show (m : ℤ) + 3 - 1 = (m : ℤ) + 2 by ring, show (m : ℤ) + 3 - 2 = (m : ℤ) + 1 by ring,
      show (m : ℤ) + 3 + 2 = (m : ℤ) + 5 by ring, show (m : ℤ) + 3 + 1 = (m : ℤ) + 4 by ring,
      e1, e2, e3, e4, e5] at h
    push_cast
    apply mul_right_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
    rw [h]; ring
  | odd m ih =>
    have e1 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 1) = (m : ℤ) + 1 := by
      have := ih (m + 1) (by omega); push_cast at this; exact this
    have e2 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 2) = (m : ℤ) + 2 := by
      have := ih (m + 2) (by omega); push_cast at this; exact this
    have e3 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 3) = (m : ℤ) + 3 := by
      have := ih (m + 3) (by omega); push_cast at this; exact this
    have e4 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 4) = (m : ℤ) + 4 := by
      have := ih (m + 4) (by omega); push_cast at this; exact this
    have h := normEDS_odd (2 : ℤ) 3 2 ((m : ℤ) + 2)
    rw [show (m : ℤ) + 2 + 2 = (m : ℤ) + 4 by ring, show (m : ℤ) + 2 - 1 = (m : ℤ) + 1 by ring,
      show (m : ℤ) + 2 + 1 = (m : ℤ) + 3 by ring, e1, e2, e3, e4] at h
    push_cast
    rw [h]; ring

theorem normEDS_two_three_two (n : ℤ) : normEDS (2 : ℤ) 3 2 n = n := by
  induction n using Int.negInduction with
  | nat n => exact normEDS_two_three_two_nat n
  | neg ih n => rw [normEDS_neg, ih]

abbrev U : Type := MvPolynomial (Fin 3) ℤ

noncomputable def P (n : ℤ) : U :=
  preNormEDS (MvPolynomial.X 0 : U) (MvPolynomial.X 1) (MvPolynomial.X 2) n

noncomputable def P4 (n : ℤ) : U :=
  preNormEDS ((MvPolynomial.X 0 : U) ^ 4) (MvPolynomial.X 1 ^ 4) (MvPolynomial.X 2 ^ 4) n

lemma P_zero : P 0 = 0 := preNormEDS_zero ..
lemma P_neg (n : ℤ) : P (-n) = -P n := preNormEDS_neg ..
lemma P_even (x : ℤ) : P (2 * x) =
    P (x - 1) ^ 2 * P x * P (x + 2) - P (x - 2) * P x * P (x + 1) ^ 2 :=
  preNormEDS_even ..

lemma normEDS_U (j : ℤ) :
    normEDS (MvPolynomial.X 0 : U) (MvPolynomial.X 1 ^ 4) (MvPolynomial.X 2 ^ 4) j =
      P4 j * if Even j then (MvPolynomial.X 0 : U) else 1 := rfl

lemma expand_P (n : ℤ) : MvPolynomial.expand 4 (P n) = P4 n := by
  simp only [P, P4, ← AlgHom.coe_toRingHom, map_preNormEDS]
  simp

lemma key (k m : ℤ) : ∃ β₁ β₂ : U,
    P ((2 * m + 1) * k) * P k =
      β₁ * (P ((m + 1) * k + 1) * P ((m + 1) * k - 1)) * P (m * k) ^ 2 -
        β₂ * (P (m * k + 1) * P (m * k - 1)) * P ((m + 1) * k) ^ 2 := by
  have h := isEllSequence_normEDS (MvPolynomial.X 0 : U) (MvPolynomial.X 1 ^ 4)
    (MvPolynomial.X 2 ^ 4) ((m + 1) * k) (m * k) 1
  rw [show (m + 1) * k + m * k = (2 * m + 1) * k by ring,
    show (m + 1) * k - m * k = k by ring, normEDS_one, one_pow, mul_one] at h
  simp only [normEDS_U] at h
  have hinj : Function.Injective (MvPolynomial.expand 4 (R := ℤ) (σ := Fin 3)) :=
    MvPolynomial.expand_injective (by norm_num)
  have hX : (MvPolynomial.X 0 : U) ≠ 0 := MvPolynomial.X_ne_zero _
  rcases Int.even_or_odd k with hk | hk
  ·
    have e1 : Even ((2 * m + 1) * k) := hk.mul_left _
    have e2 : Even (m * k) := hk.mul_left _
    have e3 : Even ((m + 1) * k) := hk.mul_left _
    have o1 : ¬Even ((m + 1) * k + 1) := by rw [Int.even_add_one]; exact not_not_intro e3
    have o2 : ¬Even ((m + 1) * k - 1) := by rw [Int.even_sub_one]; exact not_not_intro e3
    have o3 : ¬Even (m * k + 1) := by rw [Int.even_add_one]; exact not_not_intro e2
    have o4 : ¬Even (m * k - 1) := by rw [Int.even_sub_one]; exact not_not_intro e2
    rw [if_pos e1, if_pos hk, if_pos e2, if_pos e3, if_neg o1, if_neg o2, if_neg o3, if_neg o4]
      at h
    refine ⟨1, 1, hinj ?_⟩
    simp only [map_mul, map_sub, map_pow, map_one, expand_P]
    apply mul_right_cancel₀ (pow_ne_zero 2 hX)
    linear_combination h
  · have ok : ¬Even k := Int.not_even_iff_odd.mpr hk
    have o1 : ¬Even ((2 * m + 1) * k) := Int.not_even_iff_odd.mpr ((odd_two_mul_add_one m).mul hk)
    rcases Int.even_or_odd m with hm | hm
    ·
      have e2 : Even (m * k) := hm.mul_right _
      have o3 : ¬Even ((m + 1) * k) := Int.not_even_iff_odd.mpr (hm.add_one.mul hk)
      have e4 : Even ((m + 1) * k + 1) := Int.even_add_one.mpr o3
      have e5 : Even ((m + 1) * k - 1) := Int.even_sub_one.mpr o3
      have o6 : ¬Even (m * k + 1) := by rw [Int.even_add_one]; exact not_not_intro e2
      have o7 : ¬Even (m * k - 1) := by rw [Int.even_sub_one]; exact not_not_intro e2
      rw [if_neg o1, if_neg ok, if_pos e2, if_neg o3, if_pos e4, if_pos e5, if_neg o6, if_neg o7]
        at h
      refine ⟨MvPolynomial.X 0, 1, hinj ?_⟩
      simp only [map_mul, map_sub, map_pow, map_one, expand_P, MvPolynomial.expand_X]
      linear_combination h
    ·
      have o2 : ¬Even (m * k) := Int.not_even_iff_odd.mpr (hm.mul hk)
      have e3 : Even ((m + 1) * k) := (hm.add_one).mul_right _
      have o4 : ¬Even ((m + 1) * k + 1) := by rw [Int.even_add_one]; exact not_not_intro e3
      have o5 : ¬Even ((m + 1) * k - 1) := by rw [Int.even_sub_one]; exact not_not_intro e3
      have e6 : Even (m * k + 1) := Int.even_add_one.mpr o2
      have e7 : Even (m * k - 1) := Int.even_sub_one.mpr o2
      rw [if_neg o1, if_neg ok, if_neg o2, if_pos e3, if_neg o4, if_neg o5, if_pos e6, if_pos e7]
        at h
      refine ⟨1, MvPolynomial.X 0, hinj ?_⟩
      simp only [map_mul, map_sub, map_pow, map_one, expand_P, MvPolynomial.expand_X]
      linear_combination h

lemma P_ne_zero {k : ℤ} (hk : k ≠ 0) : P k ≠ 0 := by
  intro h0
  obtain ⟨ev, h1⟩ : ∃ ev : U →+* ℤ, ev (P k) = preNormEDS (16 : ℤ) 3 2 k :=
    ⟨MvPolynomial.eval ![16, 3, 2], by simp only [P, map_preNormEDS]; simp⟩
  have h16 : preNormEDS ((2 : ℤ) ^ 4) 3 2 k = preNormEDS 16 3 2 k := by norm_num
  have hd : preNormEDS ((2 : ℤ) ^ 4) 3 2 k ∣ normEDS 2 3 2 k := ⟨if Even k then 2 else 1, rfl⟩
  rw [h16, ← h1, h0, map_zero, normEDS_two_three_two, zero_dvd_iff] at hd
  exact hk hd

lemma P_dvd_P_mul (k : ℤ) (n : ℤ) : P k ∣ P (n * k) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [P_zero]
  have hPk := P_ne_zero hk
  induction n using Int.negInduction with
  | nat n =>
    induction n using Nat.evenOddStrongRec with
    | h_even j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [P_zero]
      have hj' := ih j (by omega)
      rw [show ((2 * j : ℕ) : ℤ) * k = 2 * ((j : ℤ) * k) by push_cast; ring, P_even]
      apply dvd_sub
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hj' _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hj' _) _
    | h_odd j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      obtain ⟨u, hu⟩ := ih j (by omega)
      obtain ⟨v, hv⟩ := ih (j + 1) (by omega)
      obtain ⟨β₁, β₂, hkey⟩ := key k j
      push_cast at hv ⊢
      rw [hu, hv] at hkey
      refine ⟨β₁ * (P (((j : ℤ) + 1) * k + 1) * P (((j : ℤ) + 1) * k - 1)) * u ^ 2 -
        β₂ * (P ((j : ℤ) * k + 1) * P ((j : ℤ) * k - 1)) * v ^ 2, ?_⟩
      apply mul_right_cancel₀ hPk
      linear_combination hkey
  | neg ih n => rw [neg_mul, P_neg]; exact (ih n).neg_right

theorem preNormEDS_dvd_preNormEDS_mul {R : Type u} [CommRing R] (B c d : R) (k n : ℤ) :
    preNormEDS B c d k ∣ preNormEDS B c d (n * k) := by
  obtain ⟨q, hq⟩ := P_dvd_P_mul k n
  obtain ⟨ev, hev⟩ : ∃ ev : U →+* R, ∀ j : ℤ, ev (P j) = preNormEDS B c d j :=
    ⟨MvPolynomial.eval₂Hom (Int.castRingHom R) ![B, c, d],
      fun j => by simp only [P, map_preNormEDS]; simp⟩
  refine ⟨ev q, ?_⟩
  rw [← hev, ← hev, hq, map_mul]

end PsiDvdProof

theorem solution
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) {m n : ℤ} (hmn : m ∣ n) :
    W.preΨ m ∣ W.preΨ n := by
  obtain ⟨t, rfl⟩ := hmn
  rw [mul_comm]
  exact PsiDvdProof.preNormEDS_dvd_preNormEDS_mul _ _ _ m t

end S_WeierstrassCurve_prePsi_dvd_prePsi_of_dvd
end P2MW
export P2MW.S_WeierstrassCurve_prePsi_dvd_prePsi_of_dvd (solution)
