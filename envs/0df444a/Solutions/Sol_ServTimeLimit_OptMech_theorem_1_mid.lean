-- Prove2me | solution 1 for ServTimeLimit.OptMech.theorem_1_mid
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:33:26.162917+00:00
-- url     : https://prove2.me/submissions/7d3368f5-ddad-452d-ad3b-957c14351780

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model
import Theorems.Thm_ServTimeLimit_OptMech_subproblem_4

namespace STLMid

open MeasureTheory ServTimeLimit.OptMech

/-! ### Part 1: Normalized algebraic functions and monotonicity -/

noncomputable def L (a T : ℝ) : ℝ := T - (T ^ 2 + a ^ 2) / 2
noncomputable def M (a T : ℝ) : ℝ := T ^ 2 - (2 * T ^ 3 + a ^ 3) / 3
noncomputable def D (lam a T : ℝ) : ℝ := 1 - lam * L a T
noncomputable def W (lam a T : ℝ) : ℝ := lam * M a T / (2 * D lam a T)
noncomputable def F (lam c a T : ℝ) : ℝ := L a T - c * (1 - a) * W lam a T
noncomputable def H (lam c a T : ℝ) : ℝ :=
  c * lam * (1 - a) / D lam a T * (T + W lam a T)

lemma L_nonneg {a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (hT : T ≤ 1) : 0 ≤ L a T := by
  unfold L
  have h1 : 0 ≤ (T - a) * (T + a) := by nlinarith
  have h2 : 0 ≤ T * (1 - T) := by nlinarith
  linarith

lemma M_nonneg {a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (hT : T ≤ 1) : 0 ≤ M a T := by
  unfold M
  have h1 : 0 ≤ (T - a) * (T ^ 2 + T * a + a ^ 2) :=
    mul_nonneg (by linarith) (by nlinarith)
  have h2 : 0 ≤ T ^ 2 * (1 - T) := mul_nonneg (sq_nonneg T) (by linarith)
  linarith

lemma cs_poly {a T : ℝ} (_ha : 0 ≤ a) (haT : a ≤ T) (hT : T ≤ 1) :
    L a T ^ 2 ≤ (1 - a) * M a T := by
  have hid : (1 - a) * M a T - L a T ^ 2 = (T - a) ^ 3 * (4 - 3 * T - a) / 12 := by
    unfold L M; ring
  have h1 : 0 ≤ (T - a) ^ 3 := pow_nonneg (by linarith) 3
  have h2 : 0 ≤ 4 - 3 * T - a := by linarith
  have h3 : 0 ≤ (T - a) ^ 3 * (4 - 3 * T - a) / 12 := by positivity
  linarith

lemma L_mono {a1 a2 T1 T2 : ℝ} (ha1 : 0 ≤ a1) (haa : a1 ≤ a2)
    (hTT : T2 ≤ T1) (hT1 : T1 ≤ 1) : L a2 T2 ≤ L a1 T1 := by
  have hid : L a1 T1 - L a2 T2 =
      (a2 - a1) * (a2 + a1) / 2 + (T1 - T2) * (2 - T1 - T2) / 2 := by
    unfold L; ring
  have h1 : 0 ≤ (a2 - a1) * (a2 + a1) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (T1 - T2) * (2 - T1 - T2) := mul_nonneg (by linarith) (by linarith)
  linarith

lemma M_mono {a1 a2 T1 T2 : ℝ} (ha1 : 0 ≤ a1) (haa : a1 ≤ a2)
    (hT2 : 0 ≤ T2) (hTT : T2 ≤ T1) (hT1 : T1 ≤ 1) : M a2 T2 ≤ M a1 T1 := by
  have hid : M a1 T1 - M a2 T2 =
      (a2 - a1) * (a2 ^ 2 + a2 * a1 + a1 ^ 2) / 3 +
      (T1 - T2) * ((T1 - T2) ^ 2 + 3 * T1 * (1 - T1) + 3 * T2 * (1 - T2)) / 3 := by
    unfold M; ring
  have h1 : 0 ≤ (a2 - a1) * (a2 ^ 2 + a2 * a1 + a1 ^ 2) :=
    mul_nonneg (by linarith) (by nlinarith)
  have h2 : 0 ≤ (T1 - T2) ^ 2 + 3 * T1 * (1 - T1) + 3 * T2 * (1 - T2) := by
    have : 0 ≤ (T1 - T2) ^ 2 := sq_nonneg _
    have : 0 ≤ T1 * (1 - T1) := by nlinarith
    have : 0 ≤ T2 * (1 - T2) := by nlinarith
    linarith
  have h3 : 0 ≤ (T1 - T2) * ((T1 - T2) ^ 2 + 3 * T1 * (1 - T1) + 3 * T2 * (1 - T2)) :=
    mul_nonneg (by linarith) h2
  linarith

lemma D_mono {lam a1 a2 T1 T2 : ℝ} (hlam : 0 < lam) (ha1 : 0 ≤ a1) (haa : a1 ≤ a2)
    (hTT : T2 ≤ T1) (hT1 : T1 ≤ 1) : D lam a1 T1 ≤ D lam a2 T2 := by
  unfold D
  have := L_mono ha1 haa hTT hT1
  nlinarith

lemma W_nonneg {lam a T : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a) (haT : a ≤ T) (hT : T ≤ 1)
    (hD : 0 < D lam a T) : 0 ≤ W lam a T := by
  unfold W
  have hM := M_nonneg ha haT hT
  positivity

lemma W_mono {lam a1 a2 T1 T2 : ℝ} (hlam : 0 < lam) (ha1 : 0 ≤ a1) (haa : a1 ≤ a2)
    (ha2T2 : a2 ≤ T2) (hTT : T2 ≤ T1) (hT1 : T1 ≤ 1) (hD1 : 0 < D lam a1 T1) :
    W lam a2 T2 ≤ W lam a1 T1 := by
  have hT2 : 0 ≤ T2 := by linarith
  have hM2 : 0 ≤ M a2 T2 := M_nonneg (by linarith) ha2T2 (by linarith)
  have hM : M a2 T2 ≤ M a1 T1 := M_mono ha1 haa hT2 hTT hT1
  have hD : D lam a1 T1 ≤ D lam a2 T2 := D_mono hlam ha1 haa hTT hT1
  have hD2 : 0 < D lam a2 T2 := by linarith
  unfold W
  calc lam * M a2 T2 / (2 * D lam a2 T2)
      ≤ lam * M a1 T1 / (2 * D lam a2 T2) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left hM hlam.le
    _ ≤ lam * M a1 T1 / (2 * D lam a1 T1) := by
        apply div_le_div_of_nonneg_left (by nlinarith) (by linarith) (by linarith)

lemma H_lt {lam c a1 a2 T1 T2 : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (ha1 : 0 ≤ a1) (haa : a1 ≤ a2) (ha2 : a2 < 1)
    (ha1T1 : a1 ≤ T1) (ha2T2 : a2 ≤ T2) (hTT : T2 ≤ T1) (hT1 : T1 ≤ 1)
    (hT1pos : 0 < T1) (hD1 : 0 < D lam a1 T1) (hstrict : a1 < a2 ∨ T2 < T1) :
    H lam c a2 T2 < H lam c a1 T1 := by
  have hD : D lam a1 T1 ≤ D lam a2 T2 := D_mono hlam ha1 haa hTT hT1
  have hD2 : 0 < D lam a2 T2 := by linarith
  have hW2 : 0 ≤ W lam a2 T2 := W_nonneg hlam (by linarith) ha2T2 (by linarith) hD2
  have hW1 : 0 ≤ W lam a1 T1 := W_nonneg hlam ha1 ha1T1 hT1 hD1
  have hW : W lam a2 T2 ≤ W lam a1 T1 := W_mono hlam ha1 haa ha2T2 hTT hT1 hD1
  have hT2 : 0 ≤ T2 := by linarith
  have hcl : 0 < c * lam := mul_pos hc hlam
  have ha1_1 : 0 ≤ 1 - a1 := by linarith
  have hf2 : 0 < c * lam * (1 - a2) / D lam a2 T2 := by
    have : 0 < 1 - a2 := by linarith
    positivity
  have hf_le : c * lam * (1 - a2) / D lam a2 T2 ≤ c * lam * (1 - a1) / D lam a1 T1 := by
    calc c * lam * (1 - a2) / D lam a2 T2
        ≤ c * lam * (1 - a1) / D lam a2 T2 := by
          apply div_le_div_of_nonneg_right _ hD2.le
          exact mul_le_mul_of_nonneg_left (by linarith) hcl.le
      _ ≤ c * lam * (1 - a1) / D lam a1 T1 := by
          apply div_le_div_of_nonneg_left (mul_nonneg hcl.le ha1_1) hD1 hD
  have hs_le : T2 + W lam a2 T2 ≤ T1 + W lam a1 T1 := by linarith
  have hs2 : 0 ≤ T2 + W lam a2 T2 := by linarith
  have hs1 : 0 < T1 + W lam a1 T1 := by linarith
  unfold H
  rcases hstrict with ha_lt | hT_lt
  · have hf_lt : c * lam * (1 - a2) / D lam a2 T2 < c * lam * (1 - a1) / D lam a1 T1 := by
      calc c * lam * (1 - a2) / D lam a2 T2
          < c * lam * (1 - a1) / D lam a2 T2 := by
            apply div_lt_div_of_pos_right _ hD2
            exact mul_lt_mul_of_pos_left (by linarith) hcl
        _ ≤ c * lam * (1 - a1) / D lam a1 T1 := by
            apply div_le_div_of_nonneg_left (mul_nonneg hcl.le ha1_1) hD1 hD
    calc c * lam * (1 - a2) / D lam a2 T2 * (T2 + W lam a2 T2)
        ≤ c * lam * (1 - a2) / D lam a2 T2 * (T1 + W lam a1 T1) :=
          mul_le_mul_of_nonneg_left hs_le hf2.le
      _ < c * lam * (1 - a1) / D lam a1 T1 * (T1 + W lam a1 T1) :=
          mul_lt_mul_of_pos_right hf_lt hs1
  · have hs_lt : T2 + W lam a2 T2 < T1 + W lam a1 T1 := by linarith
    calc c * lam * (1 - a2) / D lam a2 T2 * (T2 + W lam a2 T2)
        < c * lam * (1 - a2) / D lam a2 T2 * (T1 + W lam a1 T1) :=
          mul_lt_mul_of_pos_left hs_lt hf2
      _ ≤ c * lam * (1 - a1) / D lam a1 T1 * (T1 + W lam a1 T1) :=
          mul_le_mul_of_nonneg_right hf_le hs1.le

lemma H_diag_eq (lam c a : ℝ) (hD : 1 - lam * a * (1 - a) ≠ 0) :
    H lam c a a =
      c * (lam * a * (1 - a)) * (2 - lam * a * (1 - a)) /
        (2 * (1 - lam * a * (1 - a)) ^ 2) := by
  have hD' : D lam a a = 1 - lam * a * (1 - a) := by unfold D L; ring
  unfold H W
  rw [hD']
  unfold M
  field_simp [hD]
  ring

lemma H_diag_lt_half {lam c a : ℝ} (hlam : 0 < lam) (hlam4 : lam < 4) (hc : 0 < c)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hne : a ≠ 1 / 2) :
    H lam c a a < H lam c (1 / 2) (1 / 2) := by
  set x := lam * a * (1 - a)
  set y := lam * (1 / 2 : ℝ) * (1 - 1 / 2)
  have hx0 : 0 ≤ x := by positivity [show 0 ≤ 1 - a by linarith]
  have hxy : x < y := by
    have hdiff : y - x = lam * (a - 1 / 2) ^ 2 := by
      change lam * (1 / 2) * (1 - 1 / 2) - lam * a * (1 - a) = lam * (a - 1 / 2) ^ 2
      ring
    have hsq : 0 < (a - 1 / 2) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    have hpos : 0 < lam * (a - 1 / 2) ^ 2 := mul_pos hlam hsq
    linarith
  have hy1 : y < 1 := by
    change lam * (1 / 2) * (1 - 1 / 2) < 1; linarith
  have hx1 : 1 - x ≠ 0 := by linarith
  have hy1' : 1 - y ≠ 0 := by linarith
  rw [H_diag_eq lam c a hx1, H_diag_eq lam c (1 / 2) hy1']
  change c * x * (2 - x) / (2 * (1 - x) ^ 2) < c * y * (2 - y) / (2 * (1 - y) ^ 2)
  rw [← sub_pos]
  have hid : c * y * (2 - y) / (2 * (1 - y) ^ 2) - c * x * (2 - x) / (2 * (1 - x) ^ 2) =
      c * (y - x) * (2 - x - y) / (2 * (1 - x) ^ 2 * (1 - y) ^ 2) := by
    field_simp [hx1, hy1']
    ring
  rw [hid]
  have hnum : 0 < c * (y - x) * (2 - x - y) := by
    have : 0 < y - x := by linarith
    have : 0 < 2 - x - y := by linarith
    positivity
  have hden : 0 < 2 * (1 - x) ^ 2 * (1 - y) ^ 2 := by
    have : 0 < (1 - x) ^ 2 := sq_pos_of_ne_zero hx1
    have : 0 < (1 - y) ^ 2 := sq_pos_of_ne_zero hy1'
    positivity
  exact div_pos hnum hden

lemma lam2_props {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hle : lam ≤ 4 * (1 - Real.sqrt (c / (c + 2)))) :
    lam < 4 ∧ H lam c (1 / 2) (1 / 2) ≤ 1 := by
  set s := Real.sqrt (c / (c + 2)) with hs_def
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = c / (c + 2) := Real.sq_sqrt (by positivity)
  have hlam4 : lam < 4 := by linarith
  refine ⟨hlam4, ?_⟩
  set x := lam * (1 / 2 : ℝ) * (1 - 1 / 2) with hx_def
  set u := 1 - x with hu_def
  have hx_eq : x = lam / 4 := by rw [hx_def]; ring
  have hsu : s ≤ u := by rw [hu_def, hx_eq]; linarith
  have hupos : 0 < u := lt_of_lt_of_le hspos hsu
  have hu_ne : u ≠ 0 := hupos.ne'
  rw [H_diag_eq lam c (1 / 2) (by rw [← hx_def, ← hu_def]; exact hu_ne)]
  change c * x * (2 - x) / (2 * (1 - x) ^ 2) ≤ 1
  have hdiff : 1 - c * x * (2 - x) / (2 * (1 - x) ^ 2) =
      ((c + 2) * u ^ 2 - c) / (2 * u ^ 2) := by
    have hx_u : x = 1 - u := by rw [hu_def]; ring
    rw [show 1 - x = u from hu_def.symm, hx_u]
    field_simp [hu_ne]
    ring
  have hcs2 : (c + 2) * s ^ 2 = c := by
    rw [hs2]
    have hc2 : (c + 2 : ℝ) ≠ 0 := by positivity
    field_simp [hc2]
  have hsu2 : s ^ 2 ≤ u ^ 2 := by nlinarith
  have hnum : 0 ≤ (c + 2) * u ^ 2 - c := by nlinarith
  have hden : 0 < 2 * u ^ 2 := by positivity
  have hsub : 0 ≤ 1 - c * x * (2 - x) / (2 * (1 - x) ^ 2) := by
    rw [hdiff]
    exact div_nonneg hnum hden.le
  linarith

lemma lam1_ge_props {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hge : 32 * (4 * c + 5 - Real.sqrt (2 * c * (8 * c + 7))) / (3 * (26 * c + 25)) ≤ lam)
    (hD : 0 < D lam (1 / 4) 1) :
    1 ≤ H lam c (1 / 4) 1 := by
  set r := Real.sqrt (2 * c * (8 * c + 7)) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r ^ 2 = 2 * c * (8 * c + 7) := Real.sq_sqrt (by positivity)
  have hden_pos : 0 < 3 * (26 * c + 25) := by positivity
  have hlam32 : lam < 32 / 15 := by
    unfold D L at hD; linarith
  set u := 32 - 15 * lam with hu
  have hu_ne : u ≠ 0 := by rw [hu]; linarith
  have hDval : D lam (1 / 4) 1 = u / 32 := by unfold D L; rw [hu]; ring
  have hMval : M (1 / 4) 1 = 21 / 64 := by unfold M; norm_num
  have hWval : W lam (1 / 4) 1 = 21 * lam / (4 * u) := by
    unfold W; rw [hMval, hDval]; field_simp [hu_ne]; ring
  have hHval : H lam c (1 / 4) 1 = 6 * c * lam * (4 * u + 21 * lam) / u ^ 2 := by
    unfold H; rw [hDval, hWval]; field_simp [hu_ne]; ring
  have hid : 1 - H lam c (1 / 4) 1 =
      (9 * (26 * c + 25) * lam ^ 2 - 192 * (4 * c + 5) * lam + 1024) /
        (1024 * D lam (1 / 4) 1 ^ 2) := by
    rw [hHval, hDval, show 1024 * (u / 32) ^ 2 = u ^ 2 by ring]
    rw [eq_div_iff (pow_ne_zero 2 hu_ne)]
    have h1 : (1 - 6 * c * lam * (4 * u + 21 * lam) / u ^ 2) * u ^ 2 =
        u ^ 2 - 6 * c * lam * (4 * u + 21 * lam) := by
      field_simp [hu_ne]
    rw [h1, hu]
    ring
  set u1 := 32 * (4 * c + 5 - r) / (3 * (26 * c + 25))
  set u2 := 32 * (4 * c + 5 + r) / (3 * (26 * c + 25))
  have hq : 9 * (26 * c + 25) * lam ^ 2 - 192 * (4 * c + 5) * lam + 1024 =
      9 * (26 * c + 25) * (lam - u1) * (lam - u2) := by
    have h26 : (26 * c + 25 : ℝ) ≠ 0 := by positivity
    change 9 * (26 * c + 25) * lam ^ 2 - 192 * (4 * c + 5) * lam + 1024 =
      9 * (26 * c + 25) * (lam - 32 * (4 * c + 5 - r) / (3 * (26 * c + 25))) *
        (lam - 32 * (4 * c + 5 + r) / (3 * (26 * c + 25)))
    field_simp [h26]
    nlinarith [hr2]
  have hu2_gt : 32 / 15 < u2 := by
    change 32 / 15 < 32 * (4 * c + 5 + r) / (3 * (26 * c + 25))
    rw [div_lt_div_iff₀ (by norm_num) hden_pos]
    have h65 : 6 * c < 5 * r := by
      have hsq : (5 * r - 6 * c) * (5 * r + 6 * c) = 364 * c ^ 2 + 350 * c := by
        nlinarith [hr2]
      have hpos : 0 < 5 * r + 6 * c := by positivity
      have hrhs : 0 < 364 * c ^ 2 + 350 * c := by positivity
      nlinarith
    nlinarith
  have hprod : (lam - u1) * (lam - u2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hq_np : 9 * (26 * c + 25) * lam ^ 2 - 192 * (4 * c + 5) * lam + 1024 ≤ 0 := by
    rw [hq]
    have : 0 ≤ 9 * (26 * c + 25) := by positivity
    nlinarith
  have hsub : 1 - H lam c (1 / 4) 1 ≤ 0 := by
    rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg hq_np (by positivity)
  linarith

/-! ### Part 2: Partial derivatives of F -/

lemma hasDerivAt_F_T {lam c a T : ℝ} (hD : D lam a T ≠ 0) :
    HasDerivAt (fun T' => F lam c a T') ((1 - T) * (1 - H lam c a T)) T := by
  have hL : HasDerivAt (fun T' => L a T') (1 - T) T := by
    change HasDerivAt (fun T' : ℝ => T' - (T' ^ 2 + a ^ 2) / 2) (1 - T) T
    have h1 : HasDerivAt (fun T' : ℝ => T' - (T' ^ 2 + a ^ 2) / 2)
        (1 - (2 * T ^ 1 + 0) / 2) T :=
      (hasDerivAt_id T).sub (((hasDerivAt_pow 2 T).add (hasDerivAt_const T _)).div_const 2)
    convert h1 using 1; ring
  have hM : HasDerivAt (fun T' => M a T') (2 * T * (1 - T)) T := by
    change HasDerivAt (fun T' : ℝ => T' ^ 2 - (2 * T' ^ 3 + a ^ 3) / 3) (2 * T * (1 - T)) T
    have h1 : HasDerivAt (fun T' : ℝ => T' ^ 2 - (2 * T' ^ 3 + a ^ 3) / 3)
        (2 * T ^ 1 - (2 * (3 * T ^ 2) + 0) / 3) T :=
      (hasDerivAt_pow 2 T).sub
        ((((hasDerivAt_pow 3 T).const_mul 2).add (hasDerivAt_const T _)).div_const 3)
    convert h1 using 1; ring
  have hDd : HasDerivAt (fun T' => D lam a T') (-lam * (1 - T)) T := by
    change HasDerivAt (fun T' => 1 - lam * L a T') (-lam * (1 - T)) T
    have h1 : HasDerivAt (fun T' => 1 - lam * L a T') (0 - lam * (1 - T)) T :=
      (hasDerivAt_const T 1).sub (hL.const_mul lam)
    convert h1 using 1; ring
  have hW : HasDerivAt (fun T' => W lam a T')
      (((lam * (2 * T * (1 - T))) * (2 * D lam a T) -
        (lam * M a T) * (2 * (-lam * (1 - T)))) / (2 * D lam a T) ^ 2) T := by
    change HasDerivAt (fun T' => lam * M a T' / (2 * D lam a T')) _ T
    exact (hM.const_mul lam).div (hDd.const_mul 2) (mul_ne_zero two_ne_zero hD)
  have hF : HasDerivAt (fun T' => F lam c a T')
      ((1 - T) - c * (1 - a) *
        (((lam * (2 * T * (1 - T))) * (2 * D lam a T) -
          (lam * M a T) * (2 * (-lam * (1 - T)))) / (2 * D lam a T) ^ 2)) T := by
    change HasDerivAt (fun T' => L a T' - c * (1 - a) * W lam a T') _ T
    exact hL.sub (hW.const_mul (c * (1 - a)))
  convert hF using 1
  unfold H W
  field_simp [hD]
  ring

lemma hasDerivAt_F_a {lam c a T : ℝ} (hD : D lam a T ≠ 0) :
    HasDerivAt (fun a' => F lam c a' T)
      (a * (H lam c a T - 1) + c * lam / (6 * D lam a T) * (T - a) ^ 2 * (3 - 4 * a - 2 * T)) a := by
  have hL : HasDerivAt (fun a' => L a' T) (-a) a := by
    change HasDerivAt (fun a' : ℝ => T - (T ^ 2 + a' ^ 2) / 2) (-a) a
    have h1 : HasDerivAt (fun a' : ℝ => T - (T ^ 2 + a' ^ 2) / 2)
        (0 - (0 + 2 * a ^ 1) / 2) a :=
      (hasDerivAt_const a T).sub (((hasDerivAt_const a _).add (hasDerivAt_pow 2 a)).div_const 2)
    convert h1 using 1; ring
  have hM : HasDerivAt (fun a' => M a' T) (-(a ^ 2)) a := by
    change HasDerivAt (fun a' : ℝ => T ^ 2 - (2 * T ^ 3 + a' ^ 3) / 3) (-(a ^ 2)) a
    have h1 : HasDerivAt (fun a' : ℝ => T ^ 2 - (2 * T ^ 3 + a' ^ 3) / 3)
        (0 - (0 + 3 * a ^ 2) / 3) a :=
      (hasDerivAt_const a _).sub (((hasDerivAt_const a _).add (hasDerivAt_pow 3 a)).div_const 3)
    convert h1 using 1; ring
  have hDd : HasDerivAt (fun a' => D lam a' T) (lam * a) a := by
    change HasDerivAt (fun a' => 1 - lam * L a' T) (lam * a) a
    have h1 : HasDerivAt (fun a' => 1 - lam * L a' T) (0 - lam * (-a)) a :=
      (hasDerivAt_const a 1).sub (hL.const_mul lam)
    convert h1 using 1; ring
  have hW : HasDerivAt (fun a' => W lam a' T)
      (((lam * -(a ^ 2)) * (2 * D lam a T) -
        (lam * M a T) * (2 * (lam * a))) / (2 * D lam a T) ^ 2) a := by
    change HasDerivAt (fun a' => lam * M a' T / (2 * D lam a' T)) _ a
    exact (hM.const_mul lam).div (hDd.const_mul 2) (mul_ne_zero two_ne_zero hD)
  have h1a : HasDerivAt (fun a' : ℝ => c * (1 - a')) (-c) a := by
    have h1 : HasDerivAt (fun a' : ℝ => c * (1 - a')) (c * (0 - 1)) a :=
      ((hasDerivAt_const a 1).sub (hasDerivAt_id a)).const_mul c
    convert h1 using 1; ring
  have hF := hL.sub (h1a.mul hW)
  have hd_eq : -a - (-c * W lam a T + c * (1 - a) *
      ((lam * -(a ^ 2) * (2 * D lam a T) - lam * M a T * (2 * (lam * a))) /
        (2 * D lam a T) ^ 2)) =
      a * (H lam c a T - 1) + c * lam / (6 * D lam a T) * (T - a) ^ 2 * (3 - 4 * a - 2 * T) := by
    unfold H W
    have hMdef : M a T = T ^ 2 - (2 * T ^ 3 + a ^ 3) / 3 := rfl
    field_simp [hD]
    rw [hMdef]
    ring
  rw [← hd_eq]
  exact hF

/-! ### Part 3: Compactness, characterization, and uniqueness on Δ -/

lemma F_lt_zero_of_D_lt {lam c a T : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (ha : 0 ≤ a) (haT : a ≤ T) (hT : T ≤ 1)
    (hDpos : 0 < D lam a T) (hDlt : D lam a T < c / (c + 2)) :
    F lam c a T < 0 := by
  have hcs := cs_poly ha haT hT
  have hLpos : 0 < L a T := by
    have : D lam a T < 1 := lt_trans hDlt (by rw [div_lt_one (by linarith)]; linarith)
    unfold D at this; nlinarith
  have h1 : 2 * D lam a T < c * (lam * L a T) := by
    have h2 : D lam a T * (c + 2) < c := (lt_div_iff₀ (by linarith)).mp hDlt
    have h3 : lam * L a T = 1 - D lam a T := by unfold D; ring
    nlinarith
  have h2 : L a T < c * lam * L a T ^ 2 / (2 * D lam a T) := by
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  have h3 : c * lam * L a T ^ 2 / (2 * D lam a T) ≤ c * (1 - a) * W lam a T := by
    unfold W
    rw [show c * (1 - a) * (lam * M a T / (2 * D lam a T)) =
        c * lam * ((1 - a) * M a T) / (2 * D lam a T) by ring]
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hcs (by positivity)
  unfold F
  linarith

lemma exists_pos_F {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c) :
    ∃ a1 : ℝ, 0 ≤ a1 ∧ a1 ≤ 1 ∧ c / (c + 2) ≤ D lam a1 1 ∧ 0 < F lam c a1 1 := by
  set ε := min (1 / 2 : ℝ) (min (1 / (2 * lam)) (1 / (4 * c * lam)))
  have hεpos : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hε2 : ε ≤ 1 / (2 * lam) := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ 1 / (4 * c * lam) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨1 - ε, by linarith, by linarith, ?_⟩
  have hL : L (1 - ε) 1 = ε * (2 - ε) / 2 := by unfold L; ring
  have hL_le : L (1 - ε) 1 ≤ ε := by rw [hL]; nlinarith
  have hL_ge : ε / 2 ≤ L (1 - ε) 1 := by rw [hL]; nlinarith
  have hD_ge : 1 / 2 ≤ D lam (1 - ε) 1 := by
    unfold D
    have : lam * ε ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hε2 hlam.le
      have hlam_ne : lam ≠ 0 := hlam.ne'
      have : lam * (1 / (2 * lam)) = 1 / 2 := by field_simp
      linarith
    nlinarith
  have hM_le : M (1 - ε) 1 ≤ ε := by
    have : M (1 - ε) 1 = ε * (3 - 3 * ε + ε ^ 2) / 3 := by unfold M; ring
    rw [this]; nlinarith
  have hW_le : c * (1 - (1 - ε)) * W lam (1 - ε) 1 ≤ ε / 4 := by
    have hDpos : 0 < D lam (1 - ε) 1 := by linarith
    have hM0 : 0 ≤ M (1 - ε) 1 := M_nonneg (by linarith) (by linarith) le_rfl
    unfold W
    have h1 : lam * M (1 - ε) 1 / (2 * D lam (1 - ε) 1) ≤ lam * ε := by
      rw [div_le_iff₀ (by linarith)]
      have h1a : M (1 - ε) 1 ≤ ε * (2 * D lam (1 - ε) 1) := by nlinarith
      have h1b := mul_le_mul_of_nonneg_left h1a hlam.le
      linarith
    have h2 : c * ε * (lam * ε) ≤ ε / 4 := by
      have : 4 * c * lam * ε ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hε3 (show (0 : ℝ) ≤ 4 * c * lam by positivity)
        have hne : (4 * c * lam : ℝ) ≠ 0 := by positivity
        have : 4 * c * lam * (1 / (4 * c * lam)) = 1 := by field_simp
        linarith
      nlinarith
    have : 1 - (1 - ε) = ε := by ring
    rw [this]
    have h3 : c * ε * (lam * M (1 - ε) 1 / (2 * D lam (1 - ε) 1)) ≤ c * ε * (lam * ε) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hFpos : 0 < F lam c (1 - ε) 1 := by
    unfold F; linarith
  have hDgec : c / (c + 2) ≤ D lam (1 - ε) 1 := by
    by_contra hlt
    push Not at hlt
    have := F_lt_zero_of_D_lt hlam hc (by linarith) (by linarith) le_rfl (by linarith) hlt
    linarith
  exact ⟨hDgec, hFpos⟩

lemma deriv_le_zero_of_isMax_right {g : ℝ → ℝ} {x0 d : ℝ}
    (hd : HasDerivAt g d x0)
    (hmax : ∃ δ > 0, ∀ x ∈ Set.Icc x0 (x0 + δ), g x ≤ g x0) : d ≤ 0 := by
  by_contra hpos
  push Not at hpos
  obtain ⟨δ, hδ, hle⟩ := hmax
  have ht := hd.tendsto_slope_zero_right
  have hev := (ht.eventually (Ioi_mem_nhds hpos)).and (Ioo_mem_nhdsGT hδ)
  obtain ⟨h, hh1, hh2⟩ := hev.exists
  have hgh : g (x0 + h) ≤ g x0 := hle (x0 + h) ⟨by linarith [hh2.1], by linarith [hh2.2]⟩
  simp only [smul_eq_mul] at hh1
  have : 0 < h⁻¹ * (g (x0 + h) - g x0) := hh1
  have : 0 < g (x0 + h) - g x0 := by
    have hinv : 0 < h⁻¹ := inv_pos.mpr hh2.1
    nlinarith
  linarith

lemma exists_global_max {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c) :
    ∃ aStar TStar : ℝ, 0 ≤ aStar ∧ aStar ≤ TStar ∧ TStar ≤ 1 ∧ 0 < D lam aStar TStar ∧
      ∀ a T, 0 ≤ a → a ≤ T → T ≤ 1 → 0 < D lam a T →
        F lam c a T ≤ F lam c aStar TStar := by
  let Δ0 : Set (ℝ × ℝ) :=
    { p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1 ∧ c / (c + 2) ≤ D lam p.1 p.2 }
  have hDcont : Continuous (fun p : ℝ × ℝ => D lam p.1 p.2) := by
    unfold D L; fun_prop
  have hΔ0_compact : IsCompact Δ0 := by
    have hbox : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.prod isCompact_Icc
    have hsub : Δ0 ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := fun p hp =>
      ⟨⟨hp.1, hp.2.1.trans hp.2.2.1⟩, ⟨hp.1.trans hp.2.1, hp.2.2.1⟩⟩
    have hcl : IsClosed Δ0 := by
      have h1 : IsClosed { p : ℝ × ℝ | 0 ≤ p.1 } := isClosed_le continuous_const continuous_fst
      have h2 : IsClosed { p : ℝ × ℝ | p.1 ≤ p.2 } := isClosed_le continuous_fst continuous_snd
      have h3 : IsClosed { p : ℝ × ℝ | p.2 ≤ 1 } := isClosed_le continuous_snd continuous_const
      have h4 : IsClosed { p : ℝ × ℝ | c / (c + 2) ≤ D lam p.1 p.2 } :=
        isClosed_le continuous_const hDcont
      exact h1.inter (h2.inter (h3.inter h4))
    exact hbox.of_isClosed_subset hcl hsub
  obtain ⟨a1, ha10, ha11, hDa1, hFa1⟩ := exists_pos_F hlam hc
  have hΔ0_ne : Δ0.Nonempty := ⟨(a1, 1), ha10, ha11, le_rfl, hDa1⟩
  have hFcont : ContinuousOn (fun p : ℝ × ℝ => F lam c p.1 p.2) Δ0 := by
    unfold F W L M
    have hDne : ∀ p ∈ Δ0, 2 * D lam p.1 p.2 ≠ 0 := fun p hp => by
      have : 0 < c / (c + 2) := by positivity
      have : 0 < D lam p.1 p.2 := lt_of_lt_of_le this hp.2.2.2
      linarith
    refine ContinuousOn.sub (by fun_prop) ?_
    refine ContinuousOn.mul (by fun_prop) ?_
    exact ContinuousOn.div (by fun_prop) (by fun_prop) hDne
  obtain ⟨⟨aStar, TStar⟩, hpStar, hmax0⟩ := hΔ0_compact.exists_isMaxOn hΔ0_ne hFcont
  have hFpos : 0 < F lam c aStar TStar :=
    lt_of_lt_of_le hFa1 (hmax0 (show (a1, (1 : ℝ)) ∈ Δ0 from ⟨ha10, ha11, le_rfl, hDa1⟩))
  have hDstar_pos : 0 < D lam aStar TStar := lt_of_lt_of_le (by positivity) hpStar.2.2.2
  refine ⟨aStar, TStar, hpStar.1, hpStar.2.1, hpStar.2.2.1, hDstar_pos, ?_⟩
  intro a T ha haT hT hDpos
  by_cases hDge : c / (c + 2) ≤ D lam a T
  · exact hmax0 (show (a, T) ∈ Δ0 from ⟨ha, haT, hT, hDge⟩)
  · push Not at hDge
    have hneg := F_lt_zero_of_D_lt hlam hc ha haT hT hDpos hDge
    linarith

lemma max_characterization {lam c a T : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlam1 : 32 * (4 * c + 5 - Real.sqrt (2 * c * (8 * c + 7))) / (3 * (26 * c + 25)) ≤ lam)
    (hlam2 : lam ≤ 4 * (1 - Real.sqrt (c / (c + 2))))
    (ha0 : 0 ≤ a) (haT : a ≤ T) (hT1 : T ≤ 1) (hDpos : 0 < D lam a T)
    (hmax : ∀ a' T', 0 ≤ a' → a' ≤ T' → T' ≤ 1 → 0 < D lam a' T' →
      F lam c a' T' ≤ F lam c a T) :
    1 / 4 ≤ a ∧ a ≤ 1 / 2 ∧ T = (3 - 4 * a) / 2 ∧ H lam c a T = 1 := by
  obtain ⟨hlam4, hHhalf⟩ := lam2_props hlam hc hlam2
  obtain ⟨a1, ha10, ha11, hDa1, hFa1⟩ := exists_pos_F hlam hc
  have hDa1_pos : 0 < D lam a1 1 := lt_of_lt_of_le (by positivity) hDa1
  have hFpos : 0 < F lam c a T :=
    lt_of_lt_of_le hFa1 (hmax a1 1 ha10 ha11 le_rfl hDa1_pos)
  have ha_lt1 : a < 1 := by
    by_contra hge
    have haeq : a = 1 := le_antisymm (haT.trans hT1) (not_lt.mp hge)
    have hTeq : T = 1 := le_antisymm hT1 (haeq ▸ haT)
    have : F lam c 1 1 = 0 := by unfold F W L M; ring
    rw [haeq, hTeq, this] at hFpos
    exact lt_irrefl 0 hFpos
  have hDcont : Continuous (fun p : ℝ × ℝ => D lam p.1 p.2) := by
    unfold D L; fun_prop
  have hDopen : IsOpen { p : ℝ × ℝ | 0 < D lam p.1 p.2 } :=
    isOpen_lt continuous_const hDcont
  obtain ⟨δ, hδpos, hδball⟩ := Metric.isOpen_iff.mp hDopen (a, T) hDpos
  have hDT_nhds : ∀ t, |t - T| < δ → 0 < D lam a t := fun t ht =>
    hδball (show (a, t) ∈ Metric.ball (a, T) δ by
      rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
      exact max_lt hδpos ht)
  have hDa_nhds : ∀ x, |x - a| < δ → 0 < D lam x T := fun x hx =>
    hδball (show (x, T) ∈ Metric.ball (a, T) δ by
      rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
      exact max_lt hx hδpos)
  rcases eq_or_lt_of_le haT with hdiag | hstrictT
  · -- Case 1: a = T (< 1)
    have hdle : (1 - T) * (1 - H lam c a T) ≤ 0 := by
      apply deriv_le_zero_of_isMax_right (hasDerivAt_F_T hDpos.ne')
      refine ⟨min (1 - T) (δ / 2), lt_min (by linarith) (by linarith), ?_⟩
      intro t ht
      have ht1 : t ≤ 1 := by linarith [ht.2, min_le_left (1 - T) (δ / 2)]
      have htd : |t - T| < δ := by
        rw [abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.2, min_le_right (1 - T) (δ / 2)]
      exact hmax a t ha0 (haT.trans ht.1) ht1 (hDT_nhds t htd)
    have hHge1 : 1 ≤ H lam c a a := by
      rw [← hdiag] at hdle
      have h1a : 0 < 1 - a := by linarith
      nlinarith
    have ha_half : a = 1 / 2 := by
      by_contra hne
      have hlt := H_diag_lt_half hlam hlam4 hc ha0 ha_lt1.le hne
      linarith
    rw [← hdiag, ha_half]
    refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
    rw [ha_half] at hHge1
    linarith
  · -- Case a < T: split on T = 1 vs T < 1
    rcases eq_or_lt_of_le hT1 with hTeq1 | hTlt1
    · -- Case 2: a < T = 1
      subst hTeq1
      have hapos : 0 < a := by
        by_contra hle0
        have haeq0 : a = 0 := le_antisymm (not_lt.mp hle0) ha0
        have hdale : a * (H lam c a 1 - 1) +
            c * lam / (6 * D lam a 1) * (1 - a) ^ 2 * (3 - 4 * a - 2 * 1) ≤ 0 := by
          apply deriv_le_zero_of_isMax_right (hasDerivAt_F_a hDpos.ne')
          refine ⟨min (1 / 2) (δ / 2), lt_min (by norm_num) (by linarith), ?_⟩
          intro x hx
          have hx1 : x ≤ 1 := by linarith [hx.2, min_le_left (1 / 2 : ℝ) (δ / 2)]
          have hxd : |x - a| < δ := by
            rw [abs_of_nonneg (by linarith [hx.1])]
            linarith [hx.2, min_le_right (1 / 2 : ℝ) (δ / 2)]
          exact hmax x 1 (ha0.trans hx.1) hx1 le_rfl (hDa_nhds x hxd)
        rw [haeq0] at hdale
        have hD0 : 0 < D lam 0 1 := haeq0 ▸ hDpos
        have : 0 < c * lam / (6 * D lam 0 1) * (1 - 0) ^ 2 * (3 - 4 * 0 - 2 * 1) := by positivity
        linarith
      -- Show H lam c a 1 ≤ 1 by moving T slightly below 1 if H > 1
      have hHle1 : H lam c a 1 ≤ 1 := by
        by_contra hgt
        push Not at hgt
        have hHcont : ContinuousAt (fun t => H lam c a t) 1 := by
          unfold H W D L M
          have hDne : 1 - lam * (1 - (1 ^ 2 + a ^ 2) / 2) ≠ 0 := hDpos.ne'
          have h2Dne : 2 * (1 - lam * (1 - (1 ^ 2 + a ^ 2) / 2)) ≠ 0 :=
            mul_ne_zero two_ne_zero hDne
          refine ContinuousAt.mul ?_ ?_
          · exact continuousAt_const.div (by fun_prop) hDne
          · refine continuousAt_id.add ?_
            exact ContinuousAt.div (by fun_prop) (by fun_prop) h2Dne
        have hev : ∀ᶠ t in nhds (1 : ℝ), 1 < H lam c a t :=
          hHcont.eventually (Ioi_mem_nhds hgt)
        obtain ⟨δ1, hδ1pos, hδ1⟩ := Metric.eventually_nhds_iff.mp hev
        set ε := min ((1 - a) / 2) (δ1 / 2)
        have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
        have hFcont_Icc : ContinuousOn (fun t => F lam c a t) (Set.Icc (1 - ε) 1) := by
          unfold F W L M
          have hDne : ∀ t ∈ Set.Icc (1 - ε) 1, 2 * D lam a t ≠ 0 := fun t ht => by
            have := D_mono hlam ha0 le_rfl ht.2 le_rfl
            linarith
          refine ContinuousOn.sub (by fun_prop) ?_
          refine ContinuousOn.mul (by fun_prop) ?_
          exact ContinuousOn.div (by fun_prop) (by unfold D L; fun_prop) hDne
        have hanti : StrictAntiOn (fun t => F lam c a t) (Set.Icc (1 - ε) 1) := by
          apply strictAntiOn_of_deriv_neg (convex_Icc (1 - ε) 1) hFcont_Icc
          intro t ht
          rw [interior_Icc] at ht
          have hDt : 0 < D lam a t :=
            lt_of_lt_of_le hDpos (D_mono hlam ha0 le_rfl ht.2.le le_rfl)
          have hder := (hasDerivAt_F_T (c := c) hDt.ne').deriv
          rw [hder]
          have hdist : dist t 1 < δ1 := by
            rw [Real.dist_eq, abs_of_neg (by linarith [ht.2])]
            linarith [ht.1, min_le_right ((1 - a) / 2) (δ1 / 2)]
          have hHt : 1 < H lam c a t := hδ1 hdist
          exact mul_neg_of_pos_of_neg (by linarith [ht.2]) (by linarith)
        have hlt_F : F lam c a 1 < F lam c a (1 - ε) :=
          hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
        have ha_le_eps : a ≤ 1 - ε := by linarith [min_le_left ((1 - a) / 2) (δ1 / 2)]
        have hDeps : 0 < D lam a (1 - ε) :=
          lt_of_lt_of_le hDpos (D_mono hlam ha0 le_rfl (by linarith) le_rfl)
        have hle_F := hmax a (1 - ε) ha0 ha_le_eps (by linarith) hDeps
        linarith
      -- Interior in a on T = 1: ∂F/∂a = 0
      have hda0 : a * (H lam c a 1 - 1) +
          c * lam / (6 * D lam a 1) * (1 - a) ^ 2 * (3 - 4 * a - 2 * 1) = 0 := by
        have hloc : IsLocalMax (fun x => F lam c x 1) a := by
          rw [IsLocalMax, IsMaxFilter]
          set r0 := min (min a (1 - a)) δ
          have hr0 : 0 < r0 := lt_min (lt_min hapos (by linarith)) hδpos
          filter_upwards [Metric.ball_mem_nhds a hr0] with x hx
          rw [Metric.mem_ball, Real.dist_eq] at hx
          have hx_ab := abs_lt.mp hx
          have hx0 : 0 ≤ x := by
            linarith [hx_ab.1, (min_le_left _ δ).trans (min_le_left a (1 - a))]
          have hx1 : x ≤ 1 := by
            linarith [hx_ab.2, (min_le_left _ δ).trans (min_le_right a (1 - a))]
          have hxd : |x - a| < δ := lt_of_lt_of_le hx (min_le_right _ δ)
          exact hmax x 1 hx0 hx1 le_rfl (hDa_nhds x hxd)
        exact hloc.hasDerivAt_eq_zero (hasDerivAt_F_a hDpos.ne')
      have ha_le_q : a ≤ 1 / 4 := by
        by_contra hgt
        push Not at hgt
        have hterm1 : a * (H lam c a 1 - 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hapos.le (by linarith)
        have hpos_coef : 0 < c * lam / (6 * D lam a 1) * (1 - a) ^ 2 := by
          have : 0 < 1 - a := by linarith
          positivity
        have hterm2 : c * lam / (6 * D lam a 1) * (1 - a) ^ 2 * (3 - 4 * a - 2 * 1) < 0 :=
          mul_neg_of_pos_of_neg hpos_coef (by linarith)
        linarith
      have hDq : 0 < D lam (1 / 4) 1 :=
        lt_of_lt_of_le hDpos (D_mono hlam ha0 ha_le_q le_rfl le_rfl)
      have hHq : 1 ≤ H lam c (1 / 4) 1 := lam1_ge_props hlam hc hlam1 hDq
      have ha_eq_q : a = 1 / 4 := by
        rcases eq_or_lt_of_le ha_le_q with heq | hlt
        · exact heq
        · have hHlt : H lam c (1 / 4) 1 < H lam c a 1 :=
            H_lt hlam hc ha0 ha_le_q (by norm_num) ha_lt1.le (by norm_num) le_rfl le_rfl
              (by norm_num) hDpos (Or.inl hlt)
          linarith
      rw [ha_eq_q] at hHle1 ⊢
      refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
      linarith
    · -- Case 3: a < T < 1
      have hdT0 : (1 - T) * (1 - H lam c a T) = 0 := by
        have hloc : IsLocalMax (fun t => F lam c a t) T := by
          rw [IsLocalMax, IsMaxFilter]
          set r0 := min (min (T - a) (1 - T)) δ
          have hr0 : 0 < r0 := lt_min (lt_min (by linarith) (by linarith)) hδpos
          filter_upwards [Metric.ball_mem_nhds T hr0] with t ht
          rw [Metric.mem_ball, Real.dist_eq] at ht
          have ht_ab := abs_lt.mp ht
          have hta : a ≤ t := by
            linarith [ht_ab.1, (min_le_left _ δ).trans (min_le_left (T - a) (1 - T))]
          have ht1 : t ≤ 1 := by
            linarith [ht_ab.2, (min_le_left _ δ).trans (min_le_right (T - a) (1 - T))]
          have htd : |t - T| < δ := lt_of_lt_of_le ht (min_le_right _ δ)
          exact hmax a t ha0 hta ht1 (hDT_nhds t htd)
        exact hloc.hasDerivAt_eq_zero (hasDerivAt_F_T hDpos.ne')
      have hH1 : H lam c a T = 1 := by
        have : 1 - T ≠ 0 := by linarith
        have := (mul_eq_zero.mp hdT0).resolve_left this
        linarith
      have hapos : 0 < a := by
        by_contra hle0
        have haeq0 : a = 0 := le_antisymm (not_lt.mp hle0) ha0
        have hdale : a * (H lam c a T - 1) +
            c * lam / (6 * D lam a T) * (T - a) ^ 2 * (3 - 4 * a - 2 * T) ≤ 0 := by
          apply deriv_le_zero_of_isMax_right (hasDerivAt_F_a hDpos.ne')
          refine ⟨min T (δ / 2), lt_min (by linarith) (by linarith), ?_⟩
          intro x hx
          have hxT : x ≤ T := by linarith [hx.2, min_le_left T (δ / 2)]
          have hxd : |x - a| < δ := by
            rw [abs_of_nonneg (by linarith [hx.1])]
            linarith [hx.2, min_le_right T (δ / 2)]
          exact hmax x T (ha0.trans hx.1) hxT hT1 (hDa_nhds x hxd)
        rw [hH1, haeq0] at hdale
        have : 0 < c * lam / (6 * D lam 0 T) * (T - 0) ^ 2 * (3 - 4 * 0 - 2 * T) := by
          have : 0 < T - 0 := by linarith
          have : 0 < 3 - 4 * 0 - 2 * T := by linarith
          have : 0 < D lam 0 T := haeq0 ▸ hDpos
          positivity
        linarith
      have hda0 : a * (H lam c a T - 1) +
          c * lam / (6 * D lam a T) * (T - a) ^ 2 * (3 - 4 * a - 2 * T) = 0 := by
        have hloc : IsLocalMax (fun x => F lam c x T) a := by
          rw [IsLocalMax, IsMaxFilter]
          set r0 := min (min a (T - a)) δ
          have hr0 : 0 < r0 := lt_min (lt_min hapos (by linarith)) hδpos
          filter_upwards [Metric.ball_mem_nhds a hr0] with x hx
          rw [Metric.mem_ball, Real.dist_eq] at hx
          have hx_ab := abs_lt.mp hx
          have hx0 : 0 ≤ x := by
            linarith [hx_ab.1, (min_le_left _ δ).trans (min_le_left a (T - a))]
          have hxT : x ≤ T := by
            linarith [hx_ab.2, (min_le_left _ δ).trans (min_le_right a (T - a))]
          have hxd : |x - a| < δ := lt_of_lt_of_le hx (min_le_right _ δ)
          exact hmax x T hx0 hxT hT1 (hDa_nhds x hxd)
        exact hloc.hasDerivAt_eq_zero (hasDerivAt_F_a hDpos.ne')
      rw [hH1, sub_self, mul_zero, zero_add] at hda0
      have h342 : 3 - 4 * a - 2 * T = 0 := by
        have hpos : 0 < c * lam / (6 * D lam a T) * (T - a) ^ 2 := by
          have : 0 < T - a := by linarith
          positivity
        exact (mul_eq_zero.mp hda0).resolve_left hpos.ne'
      refine ⟨by linarith, by linarith, by linarith, hH1⟩

lemma exists_unique_max_mid {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlam1 : 32 * (4 * c + 5 - Real.sqrt (2 * c * (8 * c + 7))) / (3 * (26 * c + 25)) ≤ lam)
    (hlam2 : lam ≤ 4 * (1 - Real.sqrt (c / (c + 2)))) :
    ∃ aStar TStar : ℝ, 0 ≤ aStar ∧ aStar ≤ TStar ∧ TStar ≤ 1 ∧ 0 < D lam aStar TStar ∧
      (∀ a T, 0 ≤ a → a ≤ T → T ≤ 1 → 0 < D lam a T →
        F lam c a T ≤ F lam c aStar TStar) ∧
      (∀ a T, 0 ≤ a → a ≤ T → T ≤ 1 → 0 < D lam a T →
        F lam c a T = F lam c aStar TStar → a = aStar ∧ T = TStar) := by
  obtain ⟨aStar, TStar, ha0s, haTs, hT1s, hDs, hmax⟩ := exists_global_max hlam hc
  obtain ⟨hq_s, hh_s, hTeq_s, hH_s⟩ :=
    max_characterization hlam hc hlam1 hlam2 ha0s haTs hT1s hDs hmax
  refine ⟨aStar, TStar, ha0s, haTs, hT1s, hDs, hmax, ?_⟩
  intro a T ha0 haT hT1 hD hFeq
  have hmax' : ∀ a' T', 0 ≤ a' → a' ≤ T' → T' ≤ 1 → 0 < D lam a' T' →
      F lam c a' T' ≤ F lam c a T := fun a' T' h1 h2 h3 h4 => by
    rw [hFeq]; exact hmax a' T' h1 h2 h3 h4
  obtain ⟨hq, hh, hTeq, hH⟩ :=
    max_characterization hlam hc hlam1 hlam2 ha0 haT hT1 hD hmax'
  have ha_eq : a = aStar := by
    rcases lt_trichotomy a aStar with hlt | heq | hgt
    · have hTT : TStar ≤ T := by linarith
      have hHlt : H lam c aStar TStar < H lam c a T :=
        H_lt hlam hc ha0 hlt.le (by linarith) haT haTs hTT hT1 (by linarith) hD (Or.inl hlt)
      linarith
    · exact heq
    · have hTT : T ≤ TStar := by linarith
      have hHlt : H lam c a T < H lam c aStar TStar :=
        H_lt hlam hc ha0s hgt.le (by linarith) haTs haT hTT hT1s (by linarith) hDs (Or.inl hgt)
      linarith
  exact ⟨ha_eq, by linarith⟩

/-! ### Part 4: Measure-theoretic bridge and reduction of general allocations -/

lemma intOn_of_bounded_sub_Icc {S : Set ℝ} {B M : ℝ} (hS : MeasurableSet S)
    (hsub : S ⊆ Set.Icc 0 B) {f : ℝ → ℝ} (hf : Measurable f)
    (hM : ∀ θ ∈ S, |f θ| ≤ M) : IntegrableOn f S := by
  refine Measure.integrableOn_of_bounded (M := M) ?_ hf.aestronglyMeasurable ?_
  · exact ne_of_lt (lt_of_le_of_lt (measure_mono hsub) measure_Icc_lt_top)
  · rw [ae_restrict_iff' hS]
    exact Filter.Eventually.of_forall (fun θ h => by simpa [Real.norm_eq_abs] using hM θ h)

lemma welfare_eq_formula (P : Params) {Φ : Set ℝ} {t : ℝ → ℝ} (hA : IsAllocation P Φ t) :
    welfare P Φ t = P.Lam / P.θbar * (load Φ t - volume.real Φ * (P.c * waitTime P Φ t)) := by
  obtain ⟨hΦ, hsub, ht, hbd, -⟩ := hA
  have hIt : IntegrableOn t Φ := intOn_of_bounded_sub_Icc hΦ hsub ht (M := P.θbar) fun θ h => by
    rw [abs_of_nonneg (hbd θ h).1]; exact (hbd θ h).2.trans (hsub h).2
  have hIc : IntegrableOn (fun _ : ℝ => P.c * waitTime P Φ t) Φ :=
    intOn_of_bounded_sub_Icc hΦ hsub measurable_const (M := |P.c * waitTime P Φ t|)
      (fun _ _ => le_rfl)
  unfold welfare load
  rw [integral_sub hIt hIc, setIntegral_const, smul_eq_mul]

lemma load_min_Icc {a T b : ℝ} (hb : 0 < b) (_ha : 0 ≤ a) (haT : a ≤ T) (hT : T ≤ 1) :
    load (Set.Icc (a * b) b) (fun θ => min θ (T * b)) = b ^ 2 * L a T := by
  have hab : a * b ≤ b := by nlinarith
  have haTb : a * b ≤ T * b := by nlinarith
  have hTb : T * b ≤ b := by nlinarith
  have hcont : Continuous (fun θ : ℝ => min θ (T * b)) := continuous_id.min continuous_const
  unfold load
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable (a * b) (T * b))
      (hcont.intervalIntegrable (T * b) b)]
  have e1 : ∫ θ in (a * b)..(T * b), min θ (T * b) = ∫ θ in (a * b)..(T * b), θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le haTb] at hθ
    exact min_eq_left hθ.2
  have e2 : ∫ θ in (T * b)..b, min θ (T * b) = ∫ _θ in (T * b)..b, (T * b) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hTb] at hθ
    exact min_eq_right hθ.1
  rw [e1, e2, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  unfold L; ring

lemma moment2_min_Icc {a T b : ℝ} (hb : 0 < b) (_ha : 0 ≤ a) (haT : a ≤ T) (hT : T ≤ 1) :
    moment2 (Set.Icc (a * b) b) (fun θ => min θ (T * b)) = b ^ 3 * M a T := by
  have hab : a * b ≤ b := by nlinarith
  have haTb : a * b ≤ T * b := by nlinarith
  have hTb : T * b ≤ b := by nlinarith
  have hcont : Continuous (fun θ : ℝ => (min θ (T * b)) ^ 2) :=
    (continuous_id.min continuous_const).pow 2
  unfold moment2
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable (a * b) (T * b))
      (hcont.intervalIntegrable (T * b) b)]
  have e1 : ∫ θ in (a * b)..(T * b), (min θ (T * b)) ^ 2 = ∫ θ in (a * b)..(T * b), θ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le haTb] at hθ
    dsimp only; rw [min_eq_left hθ.2]
  have e2 : ∫ θ in (T * b)..b, (min θ (T * b)) ^ 2 = ∫ _θ in (T * b)..b, (T * b) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hTb] at hθ
    dsimp only; rw [min_eq_right hθ.1]
  rw [e1, e2, integral_pow, intervalIntegral.integral_const, smul_eq_mul]
  unfold M; norm_num; ring

lemma isAllocation_Icc_min (P : Params) (hP : P.Standing) {a T : ℝ}
    (ha0 : 0 ≤ a) (haT : a ≤ T) (hT1 : T ≤ 1) (hD : 0 < D (P.Lam * P.θbar) a T) :
    IsAllocation P (Set.Icc (a * P.θbar) P.θbar) (fun θ => min θ (T * P.θbar)) := by
  obtain ⟨hΛ, -, hθ⟩ := hP
  refine ⟨measurableSet_Icc, ?_, measurable_id.min measurable_const, ?_, ?_⟩
  · intro θ hθI; exact ⟨by nlinarith [hθI.1], hθI.2⟩
  · intro θ hθI
    refine ⟨le_min (by nlinarith [hθI.1]) (by nlinarith), min_le_left _ _⟩
  · rw [load_min_Icc hθ ha0 haT hT1]
    unfold D at hD
    nlinarith

lemma welfare_Icc_min (P : Params) (hP : P.Standing) {a T : ℝ}
    (ha0 : 0 ≤ a) (haT : a ≤ T) (hT1 : T ≤ 1) (hD : 0 < D (P.Lam * P.θbar) a T) :
    welfare P (Set.Icc (a * P.θbar) P.θbar) (fun θ => min θ (T * P.θbar)) =
      (P.Lam * P.θbar) * F (P.Lam * P.θbar) P.c a T := by
  have hP' := hP
  obtain ⟨hΛ, -, hθ⟩ := hP'
  have hA := isAllocation_Icc_min P hP ha0 haT hT1 hD
  rw [welfare_eq_formula P hA]
  have ha1 : a ≤ 1 := haT.trans hT1
  have hvol : volume.real (Set.Icc (a * P.θbar) P.θbar) = P.θbar * (1 - a) := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by nlinarith)]
    ring
  rw [hvol]
  unfold waitTime
  rw [load_min_Icc hθ ha0 haT hT1, moment2_min_Icc hθ ha0 haT hT1]
  unfold F W
  have hDne : D (P.Lam * P.θbar) a T ≠ 0 := hD.ne'
  have hDdef : P.θbar - P.Lam * (P.θbar ^ 2 * L a T) = P.θbar * D (P.Lam * P.θbar) a T := by
    unfold D; ring
  rw [hDdef]
  have hθne : P.θbar ≠ 0 := hθ.ne'
  field_simp [hθne, hDne]

/-- Any feasible allocation `(Φ, t)` is dominated in welfare by `(a, T) ∈ Δ`. -/
lemma alloc_reduction (P : Params) (hP : P.Standing) {Φ : Set ℝ} {t : ℝ → ℝ}
    (hA : IsAllocation P Φ t) :
    ∃ a T : ℝ, 0 ≤ a ∧ a ≤ T ∧ T ≤ 1 ∧ 0 < D (P.Lam * P.θbar) a T ∧
      welfare P Φ t ≤ (P.Lam * P.θbar) * F (P.Lam * P.θbar) P.c a T := by
  obtain ⟨hΛ, hc, hθ⟩ := hP
  have hA' := hA
  obtain ⟨hΦ, hsub, ht, hbd, hstab⟩ := hA
  set m := volume.real Φ with hm_def
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hm_le : m ≤ P.θbar := by
    have hfin : volume (Set.Icc (0 : ℝ) P.θbar) ≠ ⊤ := ne_of_lt measure_Icc_lt_top
    have h1 := measureReal_mono hsub hfin
    have h2 : volume.real (Set.Icc (0 : ℝ) P.θbar) = P.θbar := by
      rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      linarith
    rw [hm_def]; linarith
  rcases eq_or_lt_of_le hm0 with hm_eq | hm_pos
  · have hvol0 : volume Φ = 0 := by
      have hfin : volume Φ ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (measure_mono hsub) measure_Icc_lt_top)
      by_contra hne
      have hpos : 0 < volume.real Φ := ENNReal.toReal_pos hne hfin
      linarith [hm_def]
    have hL0 : load Φ t = 0 := by
      unfold load; rw [Measure.restrict_eq_zero.mpr hvol0, integral_zero_measure]
    have hW0 : welfare P Φ t = 0 := by
      rw [welfare_eq_formula P hA', hL0, ← hm_def, ← hm_eq]; ring
    refine ⟨1, 1, zero_le_one, le_rfl, le_rfl, ?_, ?_⟩
    · unfold D L; norm_num
    · rw [hW0]; unfold F W L M; norm_num
  · set a0 := P.θbar - m with ha0_def
    have ha0_nn : 0 ≤ a0 := by linarith
    have ha0_lt : a0 < P.θbar := by linarith
    set A := Φ ∩ Set.Iio a0
    set C := Φ ∩ Set.Icc a0 P.θbar
    set B := Set.Icc a0 P.θbar \ Φ
    have hAm : MeasurableSet A := hΦ.inter measurableSet_Iio
    have hCm : MeasurableSet C := hΦ.inter measurableSet_Icc
    have hBm : MeasurableSet B := measurableSet_Icc.diff hΦ
    have hAsub : A ⊆ Set.Icc 0 P.θbar := Set.inter_subset_left.trans hsub
    have hCsub : C ⊆ Set.Icc 0 P.θbar := Set.inter_subset_left.trans hsub
    have hBsub : B ⊆ Set.Icc 0 P.θbar := fun θ h => ⟨ha0_nn.trans h.1.1, h.1.2⟩
    have hΦ_eq : Φ = A ∪ C := by
      ext θ; constructor
      · intro h
        rcases lt_or_ge θ a0 with hlt | hge
        · exact Or.inl ⟨h, hlt⟩
        · exact Or.inr ⟨h, hge, (hsub h).2⟩
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    have hIcc_eq : Set.Icc a0 P.θbar = B ∪ C := by
      ext θ; constructor
      · intro h
        by_cases hmem : θ ∈ Φ
        · exact Or.inr ⟨hmem, h⟩
        · exact Or.inl ⟨h, hmem⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩) <;> exact h
    have hdisjAC : Disjoint A C := Set.disjoint_left.mpr fun θ h1 h2 => not_lt_of_ge h2.2.1 h1.2
    have hdisjBC : Disjoint B C := Set.disjoint_left.mpr fun θ h1 h2 => h1.2 h2.1
    have hfinA : volume A ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (measure_mono hAsub) measure_Icc_lt_top)
    have hfinC : volume C ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (measure_mono hCsub) measure_Icc_lt_top)
    have hfinB : volume B ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (measure_mono hBsub) measure_Icc_lt_top)
    have hvol_Icc : volume.real (Set.Icc a0 P.θbar) = m := by
      rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      linarith
    have hvol_eq : volume.real A = volume.real B := by
      have h1 : m = volume.real A + volume.real C := by
        rw [hm_def, hΦ_eq, measureReal_union hdisjAC hCm hfinA hfinC]
      have h2 : m = volume.real B + volume.real C := by
        rw [← hvol_Icc, hIcc_eq, measureReal_union hdisjBC hCm hfinB hfinC]
      linarith
    have hIt_A : IntegrableOn t A := intOn_of_bounded_sub_Icc hAm hAsub ht (M := P.θbar)
      fun θ h => by rw [abs_of_nonneg (hbd θ h.1).1]; exact (hbd θ h.1).2.trans (hsub h.1).2
    have hIt_C : IntegrableOn t C := intOn_of_bounded_sub_Icc hCm hCsub ht (M := P.θbar)
      fun θ h => by rw [abs_of_nonneg (hbd θ h.1).1]; exact (hbd θ h.1).2.trans (hsub h.1).2
    have hIt2_A : IntegrableOn (fun θ => t θ ^ 2) A :=
      intOn_of_bounded_sub_Icc hAm hAsub (ht.pow_const 2) (M := P.θbar ^ 2) fun θ h => by
        rw [abs_of_nonneg (sq_nonneg _)]
        have := (hbd θ h.1).2.trans (hsub h.1).2
        have := (hbd θ h.1).1
        nlinarith
    have hIt2_C : IntegrableOn (fun θ => t θ ^ 2) C :=
      intOn_of_bounded_sub_Icc hCm hCsub (ht.pow_const 2) (M := P.θbar ^ 2) fun θ h => by
        rw [abs_of_nonneg (sq_nonneg _)]
        have := (hbd θ h.1).2.trans (hsub h.1).2
        have := (hbd θ h.1).1
        nlinarith
    set r : ℝ := if volume.real A = 0 then 0 else (∫ θ in A, t θ) / volume.real A with hr_def
    have hr_bounds : 0 ≤ r ∧ r ≤ a0 := by
      by_cases hA0 : volume.real A = 0
      · simp [hr_def, hA0, ha0_nn]
      · have hApos : 0 < volume.real A := lt_of_le_of_ne measureReal_nonneg (Ne.symm hA0)
        simp only [hr_def, hA0, ↓reduceIte]
        have hint0 : 0 ≤ ∫ θ in A, t θ := setIntegral_nonneg hAm (fun θ h => (hbd θ h.1).1)
        have hinta : ∫ θ in A, t θ ≤ a0 * volume.real A := by
          have hIcA : IntegrableOn (fun _ : ℝ => a0) A :=
            intOn_of_bounded_sub_Icc hAm hAsub measurable_const (M := |a0|) (fun _ _ => le_rfl)
          have hle : ∫ θ in A, t θ ≤ ∫ _θ in A, a0 :=
            setIntegral_mono_on hIt_A hIcA hAm fun θ h => (hbd θ h.1).2.trans h.2.le
          rw [setIntegral_const, smul_eq_mul] at hle
          linarith
        exact ⟨div_nonneg hint0 hApos.le, (div_le_iff₀ hApos).mpr hinta⟩
    have hr_mul : r * volume.real B = ∫ θ in A, t θ := by
      rw [← hvol_eq]
      by_cases hA0 : volume.real A = 0
      · have hv0 : volume A = 0 := by
          by_contra hne
          have hpos : 0 < volume.real A := ENNReal.toReal_pos hne hfinA
          linarith
        simp [hr_def, hA0, Measure.restrict_eq_zero.mpr hv0]
      · simp only [hr_def, hA0, ↓reduceIte]
        exact div_mul_cancel₀ _ hA0
    have hr2_le : r ^ 2 * volume.real B ≤ ∫ θ in A, t θ ^ 2 := by
      rw [← hvol_eq]
      by_cases hA0 : volume.real A = 0
      · simp only [hr_def, hA0, ↓reduceIte, zero_pow two_ne_zero, zero_mul]
        exact setIntegral_nonneg hAm (fun θ _ => sq_nonneg _)
      · have hApos : 0 < volume.real A := lt_of_le_of_ne measureReal_nonneg (Ne.symm hA0)
        have hsq : 0 ≤ ∫ θ in A, (t θ - r) ^ 2 := setIntegral_nonneg hAm (fun θ _ => sq_nonneg _)
        have hIcA : IntegrableOn (fun _ : ℝ => r ^ 2) A :=
          intOn_of_bounded_sub_Icc hAm hAsub measurable_const (M := |r ^ 2|) (fun _ _ => le_rfl)
        have hexp : ∫ θ in A, (t θ - r) ^ 2 =
            (∫ θ in A, t θ ^ 2) - 2 * r * (∫ θ in A, t θ) + r ^ 2 * volume.real A := by
          have e : (fun θ => (t θ - r) ^ 2) = fun θ => (t θ ^ 2 - (2 * r) * t θ) + r ^ 2 := by
            funext θ; ring
          have i1 : IntegrableOn (fun θ => t θ ^ 2 - (2 * r) * t θ) A :=
            hIt2_A.sub (hIt_A.const_mul (2 * r))
          rw [e, integral_add i1 hIcA, integral_sub hIt2_A (hIt_A.const_mul (2 * r)),
            integral_const_mul, setIntegral_const, smul_eq_mul]
          ring
        have hr_int : ∫ θ in A, t θ = r * volume.real A := by
          rw [← hr_mul, hvol_eq]
        rw [hexp, hr_int] at hsq
        nlinarith
    classical
    let t1 : ℝ → ℝ := fun θ => if θ ∈ C then t θ else r
    have ht1_meas : Measurable t1 := Measurable.ite hCm ht measurable_const
    have ht1_bd : ∀ θ ∈ Set.Icc a0 P.θbar, 0 ≤ t1 θ ∧ t1 θ ≤ θ := by
      intro θ hθI
      by_cases hC : θ ∈ C
      · change 0 ≤ (if θ ∈ C then t θ else r) ∧ (if θ ∈ C then t θ else r) ≤ θ
        rw [if_pos hC]; exact hbd θ hC.1
      · change 0 ≤ (if θ ∈ C then t θ else r) ∧ (if θ ∈ C then t θ else r) ≤ θ
        rw [if_neg hC]; exact ⟨hr_bounds.1, hr_bounds.2.trans hθI.1⟩
    set k := load Φ t with hk_def
    have hk_eq : load (Set.Icc a0 P.θbar) t1 = k := by
      have hIt1_B : IntegrableOn t1 B :=
        intOn_of_bounded_sub_Icc hBm hBsub ht1_meas (M := P.θbar) fun θ h => by
          rw [abs_of_nonneg (ht1_bd θ h.1).1]; exact (ht1_bd θ h.1).2.trans h.1.2
      have hIt1_C : IntegrableOn t1 C :=
        intOn_of_bounded_sub_Icc hCm hCsub ht1_meas (M := P.θbar) fun θ h => by
          rw [abs_of_nonneg (ht1_bd θ h.2).1]; exact (ht1_bd θ h.2).2.trans h.2.2
      have h1 : ∫ θ in Set.Icc a0 P.θbar, t1 θ = (∫ θ in B, t1 θ) + (∫ θ in C, t1 θ) := by
        rw [hIcc_eq, setIntegral_union hdisjBC hCm hIt1_B hIt1_C]
      have hB_int : ∫ θ in B, t1 θ = r * volume.real B := by
        have hcongr : ∫ θ in B, t1 θ = ∫ _θ in B, r :=
          setIntegral_congr_fun hBm fun θ h => by
            have hnotC : θ ∉ C := fun hC => h.2 hC.1
            show (if θ ∈ C then t θ else r) = r
            rw [if_neg hnotC]
        rw [hcongr, setIntegral_const, smul_eq_mul]; ring
      have hC_int : ∫ θ in C, t1 θ = ∫ θ in C, t θ :=
        setIntegral_congr_fun hCm fun θ h => by
          show (if θ ∈ C then t θ else r) = t θ
          rw [if_pos h]
      have hΦ_int : ∫ θ in Φ, t θ = (∫ θ in A, t θ) + (∫ θ in C, t θ) := by
        rw [hΦ_eq, setIntegral_union hdisjAC hCm hIt_A hIt_C]
      unfold load at hk_def ⊢
      rw [h1, hB_int, hC_int, hr_mul, hk_def, hΦ_int]
    have hM1_le : moment2 (Set.Icc a0 P.θbar) t1 ≤ moment2 Φ t := by
      have hIt12_B : IntegrableOn (fun θ => t1 θ ^ 2) B :=
        intOn_of_bounded_sub_Icc hBm hBsub (ht1_meas.pow_const 2) (M := P.θbar ^ 2) fun θ h => by
          rw [abs_of_nonneg (sq_nonneg _)]
          have := (ht1_bd θ h.1).2.trans h.1.2
          have := (ht1_bd θ h.1).1
          nlinarith
      have hIt12_C : IntegrableOn (fun θ => t1 θ ^ 2) C :=
        intOn_of_bounded_sub_Icc hCm hCsub (ht1_meas.pow_const 2) (M := P.θbar ^ 2) fun θ h => by
          rw [abs_of_nonneg (sq_nonneg _)]
          have := (ht1_bd θ h.2).2.trans h.2.2
          have := (ht1_bd θ h.2).1
          nlinarith
      have h1 : ∫ θ in Set.Icc a0 P.θbar, t1 θ ^ 2 =
          (∫ θ in B, t1 θ ^ 2) + (∫ θ in C, t1 θ ^ 2) := by
        rw [hIcc_eq, setIntegral_union hdisjBC hCm hIt12_B hIt12_C]
      have hB_int : ∫ θ in B, t1 θ ^ 2 = r ^ 2 * volume.real B := by
        have hcongr : ∫ θ in B, t1 θ ^ 2 = ∫ _θ in B, r ^ 2 :=
          setIntegral_congr_fun hBm fun θ h => by
            have hnotC : θ ∉ C := fun hC => h.2 hC.1
            show (if θ ∈ C then t θ else r) ^ 2 = r ^ 2
            rw [if_neg hnotC]
        rw [hcongr, setIntegral_const, smul_eq_mul]; ring
      have hC_int : ∫ θ in C, t1 θ ^ 2 = ∫ θ in C, t θ ^ 2 :=
        setIntegral_congr_fun hCm fun θ h => by
          show (if θ ∈ C then t θ else r) ^ 2 = t θ ^ 2
          rw [if_pos h]
      have hΦ_int : ∫ θ in Φ, t θ ^ 2 = (∫ θ in A, t θ ^ 2) + (∫ θ in C, t θ ^ 2) := by
        rw [hΦ_eq, setIntegral_union hdisjAC hCm hIt2_A hIt2_C]
      unfold moment2
      rw [h1, hB_int, hC_int, hΦ_int]
      linarith
    have hk0 : 0 ≤ k := setIntegral_nonneg hΦ (fun θ h => (hbd θ h).1)
    have hk_ub : k ≤ (P.θbar ^ 2 - a0 ^ 2) / 2 := by
      have hIt1 : IntegrableOn t1 (Set.Icc a0 P.θbar) :=
        intOn_of_bounded_sub_Icc measurableSet_Icc (fun θ h => ⟨ha0_nn.trans h.1, h.2⟩) ht1_meas
          (M := P.θbar) fun θ h => by
            rw [abs_of_nonneg (ht1_bd θ h).1]; exact (ht1_bd θ h).2.trans h.2
      have hIid : IntegrableOn (fun θ : ℝ => θ) (Set.Icc a0 P.θbar) :=
        intOn_of_bounded_sub_Icc measurableSet_Icc (fun θ h => ⟨ha0_nn.trans h.1, h.2⟩)
          measurable_id (M := P.θbar) fun θ h => by
            rw [abs_of_nonneg (ha0_nn.trans h.1)]; exact h.2
      have hle : load (Set.Icc a0 P.θbar) t1 ≤ ∫ θ in Set.Icc a0 P.θbar, θ :=
        setIntegral_mono_on hIt1 hIid measurableSet_Icc fun θ h => (ht1_bd θ h).2
      have hid : ∫ θ in Set.Icc a0 P.θbar, θ = (P.θbar ^ 2 - a0 ^ 2) / 2 := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha0_lt.le, integral_id]
      linarith
    have hD_k : 0 < P.θbar - P.Lam * k := by linarith
    have hW_Φ_le : welfare P Φ t ≤
        P.Lam / P.θbar * (k - m * P.c * (P.Lam * moment2 (Set.Icc a0 P.θbar) t1 /
          (2 * (P.θbar - P.Lam * k)))) := by
      rw [welfare_eq_formula P hA']
      unfold waitTime
      rw [← hk_def, ← hm_def]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hdiv : P.Lam * moment2 (Set.Icc a0 P.θbar) t1 / (2 * (P.θbar - P.Lam * k)) ≤
          P.Lam * moment2 Φ t / (2 * (P.θbar - P.Lam * k)) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left hM1_le hΛ.le
      have hmc : 0 ≤ m * P.c := by positivity
      have := mul_le_mul_of_nonneg_left hdiv hmc
      linarith
    have hsub4 := ServTimeLimit.OptMech.subproblem_4 a0 P.θbar k ha0_nn ha0_lt
    rcases le_total k (a0 * (P.θbar - a0)) with hk_low | hk_high
    · have hpart1 := (hsub4.1 hk0 hk_low).2.2 t1 ht1_meas ht1_bd hk_eq
      have hm_sub : P.θbar - a0 = m := by linarith
      have hconst_int : (∫ _θ in Set.Icc a0 P.θbar, (k / (P.θbar - a0)) ^ 2) = k ^ 2 / m := by
        rw [setIntegral_const, hvol_Icc, hm_sub, smul_eq_mul]
        have hmne : m ≠ 0 := hm_pos.ne'
        field_simp [hmne]
      have hCS_m : k ^ 2 ≤ m * moment2 (Set.Icc a0 P.θbar) t1 := by
        have h1 : k ^ 2 / m ≤ moment2 (Set.Icc a0 P.θbar) t1 := by
          unfold moment2; linarith [hpart1.1, hconst_int]
        exact (div_le_iff₀ hm_pos).mp h1 |> fun h => by linarith
      have hk_q : 4 * k ≤ P.θbar ^ 2 := by
        have : 4 * (a0 * (P.θbar - a0)) ≤ P.θbar ^ 2 := by
          nlinarith [sq_nonneg (2 * a0 - P.θbar)]
        linarith
      set q := k / P.θbar ^ 2
      have hq0 : 0 ≤ q := div_nonneg hk0 (by positivity)
      have hq4 : 4 * q ≤ 1 := by
        change 4 * (k / P.θbar ^ 2) ≤ 1
        rw [show 4 * (k / P.θbar ^ 2) = (4 * k) / P.θbar ^ 2 by ring, div_le_one (by positivity)]
        exact hk_q
      set s := Real.sqrt (1 - 4 * q)
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hs1 : s ≤ 1 := by
        calc s ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
          _ = 1 := Real.sqrt_one
      have hs2 : s ^ 2 = 1 - 4 * q := Real.sq_sqrt (by linarith)
      set a := (1 - s) / 2 with ha_def
      have ha0' : 0 ≤ a := by rw [ha_def]; linarith
      have ha1' : a ≤ 1 := by rw [ha_def]; linarith
      have hLa : L a a = q := by
        unfold L
        have : a * (1 - a) = (1 - s ^ 2) / 4 := by rw [ha_def]; ring
        have hL' : a - (a ^ 2 + a ^ 2) / 2 = a * (1 - a) := by ring
        rw [hL', this, hs2]; ring
      have hMa : (1 - a) * M a a = q ^ 2 := by
        have hM' : M a a = a ^ 2 * (1 - a) := by unfold M; ring
        have h1 : (1 - a) * M a a = (a * (1 - a)) ^ 2 := by rw [hM']; ring
        have h2 : a * (1 - a) = q := by
          have : a - (a ^ 2 + a ^ 2) / 2 = a * (1 - a) := by ring
          unfold L at hLa; linarith
        rw [h1, h2]
      have hDa : 0 < D (P.Lam * P.θbar) a a := by
        unfold D; rw [hLa]
        change 0 < 1 - P.Lam * P.θbar * (k / P.θbar ^ 2)
        have hθne : P.θbar ≠ 0 := hθ.ne'
        have : 1 - P.Lam * P.θbar * (k / P.θbar ^ 2) = (P.θbar - P.Lam * k) / P.θbar := by
          field_simp [hθne]
        rw [this]; exact div_pos hD_k hθ
      refine ⟨a, a, ha0', le_rfl, ha1', hDa, ?_⟩
      have hF_eq : (P.Lam * P.θbar) * F (P.Lam * P.θbar) P.c a a =
          P.Lam / P.θbar * (k - P.c * (P.Lam * k ^ 2 / (2 * (P.θbar - P.Lam * k)))) := by
        unfold F W D
        rw [show P.c * (1 - a) * ((P.Lam * P.θbar) * M a a / (2 * (1 - P.Lam * P.θbar * L a a))) =
            P.c * (P.Lam * P.θbar) * ((1 - a) * M a a) / (2 * (1 - P.Lam * P.θbar * L a a)) by ring]
        rw [hLa, hMa]
        have hθne : P.θbar ≠ 0 := hθ.ne'
        have hDne : P.θbar - P.Lam * k ≠ 0 := hD_k.ne'
        change P.Lam * P.θbar * (k / P.θbar ^ 2 -
          P.c * (P.Lam * P.θbar) * (k / P.θbar ^ 2) ^ 2 /
            (2 * (1 - P.Lam * P.θbar * (k / P.θbar ^ 2)))) = _
        have hDne2 : 1 - P.Lam * P.θbar * (k / P.θbar ^ 2) ≠ 0 := by
          have : 1 - P.Lam * P.θbar * (k / P.θbar ^ 2) = (P.θbar - P.Lam * k) / P.θbar := by
            field_simp [hθne]
          rw [this]; exact div_ne_zero hDne hθne
        field_simp [hθne, hDne, hDne2]
      rw [hF_eq]
      refine hW_Φ_le.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : P.c * (P.Lam * k ^ 2 / (2 * (P.θbar - P.Lam * k))) ≤
          m * P.c * (P.Lam * moment2 (Set.Icc a0 P.θbar) t1 / (2 * (P.θbar - P.Lam * k))) := by
        rw [show m * P.c * (P.Lam * moment2 (Set.Icc a0 P.θbar) t1 / (2 * (P.θbar - P.Lam * k))) =
            P.c * (P.Lam * (m * moment2 (Set.Icc a0 P.θbar) t1) / (2 * (P.θbar - P.Lam * k))) by
              ring]
        apply mul_le_mul_of_nonneg_left _ hc.le
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left hCS_m hΛ.le
      linarith
    · set T0 := P.θbar - Real.sqrt (P.θbar ^ 2 - a0 ^ 2 - 2 * k)
      obtain ⟨ha0T0, hT0b, hmin_k, hmin_opt⟩ := hsub4.2 hk_high hk_ub T0 rfl
      have hM_min := (hmin_opt t1 ht1_meas ht1_bd hk_eq).1
      set a := a0 / P.θbar
      set T := T0 / P.θbar
      have ha0' : 0 ≤ a := div_nonneg ha0_nn hθ.le
      have haT' : a ≤ T := div_le_div_of_nonneg_right ha0T0 hθ.le
      have hT1' : T ≤ 1 := (div_le_one hθ).mpr hT0b
      have hθne : P.θbar ≠ 0 := hθ.ne'
      have ha_mul : a * P.θbar = a0 := div_mul_cancel₀ a0 hθne
      have hT_mul : T * P.θbar = T0 := div_mul_cancel₀ T0 hθne
      have hL_eq : P.θbar ^ 2 * L a T = k := by
        have := load_min_Icc hθ ha0' haT' hT1'
        rw [ha_mul, hT_mul] at this
        unfold load at this
        linarith
      have hM_eq : P.θbar ^ 3 * M a T = ∫ θ in Set.Icc a0 P.θbar, (min θ T0) ^ 2 := by
        have := moment2_min_Icc hθ ha0' haT' hT1'
        rw [ha_mul, hT_mul] at this
        exact this.symm
      have hDa : 0 < D (P.Lam * P.θbar) a T := by
        unfold D
        have : 1 - P.Lam * P.θbar * L a T = (P.θbar - P.Lam * k) / P.θbar := by
          have : P.Lam * P.θbar * L a T = P.Lam * (P.θbar ^ 2 * L a T) / P.θbar := by
            field_simp [hθne]
          rw [this, hL_eq]; field_simp [hθne]
        rw [this]; exact div_pos hD_k hθ
      refine ⟨a, T, ha0', haT', hT1', hDa, ?_⟩
      have hM_le_t1 : P.θbar ^ 3 * M a T ≤ moment2 (Set.Icc a0 P.θbar) t1 := by
        unfold moment2; linarith
      have hm_eq_1a : m = P.θbar * (1 - a) := by
        have : P.θbar * (1 - a) = P.θbar - a * P.θbar := by ring
        rw [this, ha_mul]; linarith
      have hF_eq : (P.Lam * P.θbar) * F (P.Lam * P.θbar) P.c a T =
          P.Lam / P.θbar * (k - m * P.c * (P.Lam * (P.θbar ^ 3 * M a T) /
            (2 * (P.θbar - P.Lam * k)))) := by
        rw [hm_eq_1a]
        unfold F W
        have hDne : D (P.Lam * P.θbar) a T ≠ 0 := hDa.ne'
        have hDdef : P.θbar - P.Lam * k = P.θbar * D (P.Lam * P.θbar) a T := by
          rw [← hL_eq]; unfold D; ring
        rw [hDdef, ← hL_eq]
        field_simp [hθne, hDne]
      rw [hF_eq]
      refine hW_Φ_le.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : P.Lam * (P.θbar ^ 3 * M a T) / (2 * (P.θbar - P.Lam * k)) ≤
          P.Lam * moment2 (Set.Icc a0 P.θbar) t1 / (2 * (P.θbar - P.Lam * k)) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left hM_le_t1 hΛ.le
      have hmc : 0 ≤ m * P.c := by positivity
      have := mul_le_mul_of_nonneg_left this hmc
      linarith

end STLMid

open MeasureTheory ServTimeLimit.OptMech in
theorem solution (P : Params) (hP : P.Standing) (hΛ1 : lam1 P ≤ P.Lam)
    (hΛ2 : P.Lam ≤ lam2 P) :
    ∃! q : ℝ × ℝ, (0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ P.θbar) ∧
      IsFirstBest P (Set.Icc q.1 P.θbar) (fun θ => min θ q.2) := by
  have hP' := hP
  obtain ⟨hΛpos, hc, hθ⟩ := hP'
  set lam := P.Lam * P.θbar with hlam_def
  have hlam_pos : 0 < lam := mul_pos hΛpos hθ
  have hθne : P.θbar ≠ 0 := hθ.ne'
  have hlam_ge1 :
      32 * (4 * P.c + 5 - Real.sqrt (2 * P.c * (8 * P.c + 7))) / (3 * (26 * P.c + 25)) ≤ lam := by
    unfold lam1 at hΛ1
    rw [hlam_def]
    have h1 := mul_le_mul_of_nonneg_right hΛ1 hθ.le
    have h2 : 32 * (4 * P.c + 5 - Real.sqrt (2 * P.c * (8 * P.c + 7))) /
        (3 * (26 * P.c + 25) * P.θbar) * P.θbar =
        32 * (4 * P.c + 5 - Real.sqrt (2 * P.c * (8 * P.c + 7))) / (3 * (26 * P.c + 25)) := by
      field_simp [hθne]
    linarith
  have hlam_le2 : lam ≤ 4 * (1 - Real.sqrt (P.c / (P.c + 2))) := by
    unfold lam2 at hΛ2
    rw [hlam_def]
    have h1 := mul_le_mul_of_nonneg_right hΛ2 hθ.le
    have h2 : 4 * (1 - Real.sqrt (P.c / (P.c + 2))) / P.θbar * P.θbar =
        4 * (1 - Real.sqrt (P.c / (P.c + 2))) := by
      field_simp [hθne]
    linarith
  obtain ⟨aStar, TStar, haStar0, haStarT, hTStar1, hDstar, hmax, huniq⟩ :=
    STLMid.exists_unique_max_mid hlam_pos hc hlam_ge1 hlam_le2
  have hFB_star :
      IsFirstBest P (Set.Icc (aStar * P.θbar) P.θbar) (fun θ => min θ (TStar * P.θbar)) := by
    refine ⟨STLMid.isAllocation_Icc_min P hP haStar0 haStarT hTStar1 hDstar, ?_⟩
    intro Φ' t' hA'
    obtain ⟨a', T', ha0', haT', hT1', hD', hle'⟩ := STLMid.alloc_reduction P hP hA'
    rw [STLMid.welfare_Icc_min P hP haStar0 haStarT hTStar1 hDstar]
    exact hle'.trans (mul_le_mul_of_nonneg_left (hmax a' T' ha0' haT' hT1' hD') hlam_pos.le)
  refine ⟨(aStar * P.θbar, TStar * P.θbar),
    ⟨⟨by nlinarith, by nlinarith, by nlinarith⟩, hFB_star⟩, ?_⟩
  rintro ⟨θl, T0⟩ ⟨⟨hθl0, hθlT, hT0b⟩, hFB⟩
  set a := θl / P.θbar
  set T := T0 / P.θbar
  have ha_mul : a * P.θbar = θl := div_mul_cancel₀ θl hθne
  have hT_mul : T * P.θbar = T0 := div_mul_cancel₀ T0 hθne
  have ha0 : 0 ≤ a := div_nonneg hθl0 hθ.le
  have haT : a ≤ T := div_le_div_of_nonneg_right hθlT hθ.le
  have hT1 : T ≤ 1 := (div_le_one hθ).mpr hT0b
  have hDa : 0 < STLMid.D lam a T := by
    have hstab := hFB.1.2.2.2.2
    rw [← ha_mul, ← hT_mul, STLMid.load_min_Icc hθ ha0 haT hT1] at hstab
    unfold STLMid.D
    rw [hlam_def]
    have : 1 - P.Lam * P.θbar * STLMid.L a T =
        (P.θbar - P.Lam * (P.θbar ^ 2 * STLMid.L a T)) / P.θbar := by
      field_simp [hθne]
    rw [this]
    exact div_pos (by linarith) hθ
  have hweq : welfare P (Set.Icc θl P.θbar) (fun θ => min θ T0) =
      welfare P (Set.Icc (aStar * P.θbar) P.θbar) (fun θ => min θ (TStar * P.θbar)) :=
    le_antisymm (hFB_star.2 _ _ hFB.1) (hFB.2 _ _ hFB_star.1)
  rw [← ha_mul, ← hT_mul, STLMid.welfare_Icc_min P hP ha0 haT hT1 hDa,
    STLMid.welfare_Icc_min P hP haStar0 haStarT hTStar1 hDstar] at hweq
  have hFeq : STLMid.F lam P.c a T = STLMid.F lam P.c aStar TStar :=
    mul_left_cancel₀ hlam_pos.ne' hweq
  obtain ⟨ha_eq, hT_eq⟩ := huniq a T ha0 haT hT1 hDa hFeq
  ext
  · dsimp only; rw [← ha_mul, ha_eq]
  · dsimp only; rw [← hT_mul, hT_eq]
