-- Prove2me | solution 1 for OWMR.arb_local_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T12:52:25.016468+00:00
-- url     : https://prove2.me/submissions/1b38fcef-bea9-47d1-a207-05b1342f5b2c

import Definitions.Def_owmr_consolidation_policy

open OWMR

/-- The degree-six polynomial in `e = 1/m` controlling the common endpoint value. -/
private lemma key_poly (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 ≤ 29622272 * e ^ 6 + 298926080 * e ^ 5 - 456354176 * e ^ 4 - 7810462924 * e ^ 3
      - 13384023377 * e ^ 2 + 5671034918 * e + 16521966059 := by
  have h3 : e ^ 3 ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 (by norm_num)
  have h4 : e ^ 4 ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 (by norm_num)
  have h5 : 0 ≤ e ^ 5 := pow_nonneg he0 5
  have h6 : 0 ≤ e ^ 6 := pow_nonneg he0 6
  have h7 : 0 ≤ e - e ^ 2 := by nlinarith
  nlinarith [h3, h4, h5, h6, h7]

theorem solution (m : ℝ) (hm : 1 ≤ m) (u : ℝ) :
    (0 ≤ u → u ≤ conU m →
      1 + 7 * (1 + 1 / m) / 16 + (14 / (3 * conZeta m) - 1) * u
        + 3 / 8 * ((1 - u) / (1 - u / (conZeta m * (conB m - 1 + u)))) ≤ conB m) ∧
    (conU m ≤ u → u ≤ 1 →
      1 + 7 * (1 + 1 / m) / 8 + (7 / (3 * conZeta m) - 1 - 7 * (1 / m) / 12) * u
        + 3 / 8 * ((1 - u) / (1 - u / (conZeta m * (conB m - 1 + u)))) ≤ conB m) := by
  have hm0 : 0 < m := by linarith
  obtain ⟨e, he0, he1, rfl⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ m = 1 / e :=
    ⟨1 / m, by positivity, (div_le_one hm0).2 hm, by field_simp⟩
  simp only [one_div_one_div]
  have hq : 0 < 247 + 32 * e := by positivity
  have hp : 0 < 133 + 32 * e := by positivity
  have hW : 0 < 32 * e ^ 2 + 375 * e + 532 := by positivity
  have hg : conG (1 / e) = (247 + 32 * e) / 114 := by
    unfold conG conGammaBar; field_simp; ring
  have hζ : conZeta (1 / e) = (247 + 32 * e) / (133 + 32 * e) := by
    unfold conZeta; rw [hg]
    have h1 : (247 + 32 * e) / 114 - 1 = (133 + 32 * e) / 114 := by ring
    rw [h1, div_div_div_cancel_right₀ (by norm_num : (114:ℝ) ≠ 0)]
  have hB : conB (1 / e) = (133 + 32 * e) / 57 := by unfold conB; rw [hg]; ring
  have hU : conU (1 / e) = 3 * (247 + 32 * e) * (1 + e) / (4 * (32 * e ^ 2 + 375 * e + 532)) := by
    unfold conU; rw [hζ]; field_simp; ring
  have hr : ∀ u : ℝ, 0 ≤ u → (1 - u) / (1 - u / (conZeta (1 / e) * (conB (1 / e) - 1 + u)))
      = (1 - u) * (247 + 32 * e) * (76 + 32 * e + 57 * u)
        / ((247 + 32 * e) * (76 + 32 * e) + 6498 * u) := by
    intro u hu
    have hκ : conZeta (1 / e) * (conB (1 / e) - 1 + u)
        = (247 + 32 * e) * (76 + 32 * e + 57 * u) / (57 * (133 + 32 * e)) := by
      rw [hζ, hB]; field_simp; ring
    have hK : 0 < (247 + 32 * e) * (76 + 32 * e + 57 * u) := by positivity
    have hD : 0 < (247 + 32 * e) * (76 + 32 * e) + 6498 * u := by positivity
    rw [hκ, div_div_eq_mul_div, one_sub_div hK.ne', div_div_eq_mul_div,
      div_eq_div_iff (by nlinarith) hD.ne']
    ring
  -- the quadratic numerators and their common value at `u*`
  set q : ℝ := 247 + 32 * e with hqdef
  set W : ℝ := 4 * (32 * e ^ 2 + 375 * e + 532) with hWdef
  set Us : ℝ := 3 * q * (1 + e) with hUsdef
  set P6 : ℝ := 29622272 * e ^ 6 + 298926080 * e ^ 5 - 456354176 * e ^ 4 - 7810462924 * e ^ 3
      - 13384023377 * e ^ 2 + 5671034918 * e + 16521966059 with hP6
  have hP6n : 0 ≤ P6 := key_poly e he0.le he1
  have hW0 : 0 < W := by positivity
  have hUsW : W ≤ 4 * Us := by rw [hWdef, hUsdef, hqdef]; nlinarith
  have hustar : conU (1 / e) = Us / W := by rw [hU, hUsdef, hWdef]
  refine ⟨fun hu0 huU => ?_, fun huU hu1 => ?_⟩
  · -- the half-cycle envelope
    have hu1 : u * W ≤ Us := by rw [hustar, le_div_iff₀ hW0] at huU; linarith
    rw [hr u hu0, hζ, hB]
    set a2 : ℝ := 3249 * (3072 * e ^ 2 - 59584 * e - 157757) with ha2
    set a1 : ℝ := -19 * q * (80896 * e ^ 2 + 405061 * e + 499624) with ha1
    set a0 : ℝ := 2 * (8 * e + 19) * q ^ 2 * (113 * e + 475) with ha0
    have ha2n : a2 ≤ 0 := by rw [ha2]; nlinarith
    have ha1n : a1 ≤ 0 := by rw [ha1, hqdef]; nlinarith [hq]
    have hden : 0 < 912 * q * (512 * e ^ 2 + 5168 * e + 3249 * u + 9386) := by positivity
    have hid : W ^ 2 * (a2 * u ^ 2 + a1 * u + a0)
        = q ^ 2 * P6 + (W * u - Us) * (a2 * (W * u + Us) + a1 * W) := by
      rw [ha2, ha1, ha0, hP6, hWdef, hUsdef, hqdef]; ring
    have hN : 0 ≤ a2 * u ^ 2 + a1 * u + a0 := by
      have h1 : 0 ≤ (W * u - Us) * (a2 * (W * u + Us) + a1 * W) := by
        apply mul_nonneg_of_nonpos_of_nonpos
        · linarith
        · have : 0 ≤ W * u + Us := by positivity
          nlinarith
      have h2 : 0 ≤ W ^ 2 * (a2 * u ^ 2 + a1 * u + a0) := by
        rw [hid]; have := mul_nonneg (sq_nonneg q) hP6n; linarith
      by_contra hcon
      rw [not_le] at hcon
      have := mul_neg_of_pos_of_neg (pow_pos hW0 2) hcon
      linarith
    have hkey : (133 + 32 * e) / 57 - (1 + 7 * (1 + e) / 16
        + (14 / (3 * ((247 + 32 * e) / (133 + 32 * e))) - 1) * u
        + 3 / 8 * ((1 - u) * (247 + 32 * e) * (76 + 32 * e + 57 * u)
          / ((247 + 32 * e) * (76 + 32 * e) + 6498 * u)))
        = (a2 * u ^ 2 + a1 * u + a0) / (912 * q * (512 * e ^ 2 + 5168 * e + 3249 * u + 9386)) := by
      rw [ha2, ha1, ha0, hqdef]
      have h1 : (0:ℝ) < (247 + 32 * e) * (76 + 32 * e) + 6498 * u := by positivity
      field_simp
      ring
    have := div_nonneg hN hden.le
    linarith
  · -- the full-cycle envelope
    have hUs0 : 0 < Us := by positivity
    have hu1' : Us ≤ u * W := by rw [hustar, div_le_iff₀ hW0] at huU; linarith
    have hu0 : 0 ≤ u := by nlinarith
    rw [hr u hu0, hζ, hB]
    set b2 : ℝ := 3249 * (20096 * e ^ 2 + 139916 * e + 125267) with hb2
    set b1 : ℝ := 19 * q * (14336 * e ^ 3 + 121152 * e ^ 2 + 164046 * e - 1805) with hb1
    set b0 : ℝ := -4 * (8 * e + 19) * q ^ 2 * (143 * e - 38) with hb0
    have hb2p : 0 < b2 := by rw [hb2]; positivity
    have hb21 : 0 ≤ b2 / 2 + b1 := by
      have : b2 / 2 + b1 = 19 * (917504 * e ^ 4 + 14835712 * e ^ 3 + 73784448 * e ^ 2
          + 104848840 * e + 20528987) / 2 := by rw [hb2, hb1, hqdef]; ring
      rw [this]; positivity
    have hden : 0 < 912 * q * (512 * e ^ 2 + 5168 * e + 3249 * u + 9386) := by positivity
    have hid : W ^ 2 * (b2 * u ^ 2 + b1 * u + b0)
        = q ^ 2 * P6 + (W * u - Us) * (b2 * (W * u + Us) + b1 * W) := by
      rw [hb2, hb1, hb0, hP6, hWdef, hUsdef, hqdef]; ring
    have hN : 0 ≤ b2 * u ^ 2 + b1 * u + b0 := by
      have h1 : 0 ≤ (W * u - Us) * (b2 * (W * u + Us) + b1 * W) := by
        apply mul_nonneg
        · linarith
        · have h3 : W / 2 ≤ W * u + Us := by linarith
          have h4 : b2 * (W / 2) ≤ b2 * (W * u + Us) := mul_le_mul_of_nonneg_left h3 hb2p.le
          have h5 : 0 ≤ W * (b2 / 2 + b1) := mul_nonneg hW0.le hb21
          nlinarith
      have h2 : 0 ≤ W ^ 2 * (b2 * u ^ 2 + b1 * u + b0) := by
        rw [hid]; nlinarith [mul_nonneg (sq_nonneg q) hP6n]
      by_contra hcon
      rw [not_le] at hcon
      have := mul_neg_of_pos_of_neg (pow_pos hW0 2) hcon
      linarith
    have hkey : (133 + 32 * e) / 57 - (1 + 7 * (1 + e) / 8
        + (7 / (3 * ((247 + 32 * e) / (133 + 32 * e))) - 1 - 7 * e / 12) * u
        + 3 / 8 * ((1 - u) * (247 + 32 * e) * (76 + 32 * e + 57 * u)
          / ((247 + 32 * e) * (76 + 32 * e) + 6498 * u)))
        = (b2 * u ^ 2 + b1 * u + b0) / (912 * q * (512 * e ^ 2 + 5168 * e + 3249 * u + 9386)) := by
      rw [hb2, hb1, hb0, hqdef]
      have h1 : (0:ℝ) < (247 + 32 * e) * (76 + 32 * e) + 6498 * u := by positivity
      field_simp
      ring
    have := div_nonneg hN hden.le
    linarith
