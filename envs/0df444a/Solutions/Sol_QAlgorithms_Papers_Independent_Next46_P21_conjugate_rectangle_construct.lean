-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P21.conjugate_rectangle_construct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:33:44.171206+00:00
-- url     : https://prove2.me/submissions/3577e339-9db8-4814-b1e8-8238a89ce281

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21
noncomputable section
open QAlgorithms.Papers.Independent.Next46.P21
open Set
open scoped ComplexConjugate

theorem g64a_qr (a : Zsqrtd 2) : quadraticReal a = (a.re : ℝ) + (a.im : ℝ) * Real.sqrt 2 := by
  simp [quadraticReal, Zsqrtd.toReal_apply]

theorem g64a_qrs (a : Zsqrtd 2) : quadraticReal (star a) = (a.re : ℝ) - (a.im : ℝ) * Real.sqrt 2 := by
  rw [g64a_qr]; simp; ring

theorem g64a_s2 : (1.41 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.42 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem g64a_base (x y : ℝ) :
    x < quadraticReal (basePoint x y) ∧ quadraticReal (basePoint x y) ≤ x + 1 + Real.sqrt 2 ∧
    y < quadraticReal (star (basePoint x y)) ∧ quadraticReal (star (basePoint x y)) ≤ y + Real.sqrt 2 := by
  obtain ⟨s1, s2⟩ := g64a_s2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h2s : (0:ℝ) < 2 * Real.sqrt 2 := by linarith
  set a : ℤ := Int.floor ((x + y + Real.sqrt 2) / 2) + 1 with ha
  set b : ℤ := Int.floor ((x - y - Real.sqrt 2) / (2 * Real.sqrt 2)) + 1 with hb
  have ha1 := Int.floor_le ((x + y + Real.sqrt 2) / 2)
  have ha2 := Int.lt_floor_add_one ((x + y + Real.sqrt 2) / 2)
  have hb1 := Int.floor_le ((x - y - Real.sqrt 2) / (2 * Real.sqrt 2))
  have hb2 := Int.lt_floor_add_one ((x - y - Real.sqrt 2) / (2 * Real.sqrt 2))
  have ea : ((Int.floor ((x + y + Real.sqrt 2) / 2) : ℤ) : ℝ) = (a : ℝ) - 1 := by
    rw [ha]; push_cast; ring
  have eb : ((Int.floor ((x - y - Real.sqrt 2) / (2 * Real.sqrt 2)) : ℤ) : ℝ) = (b : ℝ) - 1 := by
    rw [hb]; push_cast; ring
  rw [ea] at ha1 ha2; rw [eb] at hb1 hb2
  rw [le_div_iff₀ (by norm_num)] at ha1
  rw [div_lt_iff₀ (by norm_num)] at ha2
  rw [le_div_iff₀ h2s] at hb1
  rw [div_lt_iff₀ h2s] at hb2
  have key : basePoint x y = if (a : ℝ) - (b : ℝ) * Real.sqrt 2 ≤ y + Real.sqrt 2 then ⟨a, b⟩
      else if (a : ℝ) + (b : ℝ) * Real.sqrt 2 ≤ x + 1 then ⟨a, b + 1⟩ else ⟨a - 1, b⟩ := rfl
  rw [key]
  split_ifs with c1 c2
  · rw [g64a_qrs, g64a_qr]; dsimp only
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rw [g64a_qrs, g64a_qr]; dsimp only; push_cast
    push Not at c1
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rw [g64a_qrs, g64a_qr]; dsimp only; push_cast
    push Not at c1 c2
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem g64a_mem (x0 x1 y0 y1 : ℝ) (a : Zsqrtd 2) : a ∈ rectangleSolutions x0 x1 y0 y1 ↔
    (x0 ≤ quadraticReal a ∧ quadraticReal a ≤ x1) ∧
    (y0 ≤ quadraticReal (star a) ∧ quadraticReal (star a) ≤ y1) := Iff.rfl

theorem g64a_norm (x0 x1 y0 y1 : ℝ) (h1 : 1 < x1 - x0) (h2 : x1 - x0 ≤ scaleUnit)
    (hw : scaleUnit ^ 2 ≤ (x1 - x0) * (y1 - y0)) :
    normalizedPoint x0 y0 (x1 - x0) ∈ rectangleSolutions x0 x1 y0 y1 := by
  obtain ⟨s1, s2⟩ := g64a_s2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  rw [scaleUnit] at h2 hw
  unfold normalizedPoint
  split_ifs with hd
  · obtain ⟨b1, b2, b3, b4⟩ := g64a_base y0 x0
    have hw' : 1 + Real.sqrt 2 ≤ y1 - y0 := by
      by_contra h; push Not at h; nlinarith
    rw [g64a_mem, star_star]
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · push Not at hd
    obtain ⟨b1, b2, b3, b4⟩ := g64a_base (-scaleUnit * (x0 + 1)) (y0 / scaleUnit)
    generalize basePoint (-scaleUnit * (x0 + 1)) (y0 / scaleUnit) = c at *
    rw [scaleUnit] at b1 b2 b3 b4
    have hw' : 2 + Real.sqrt 2 ≤ y1 - y0 := by
      by_contra h; push Not at h; nlinarith
    have hμ : (0:ℝ) < 1 + Real.sqrt 2 := by linarith
    have e1 : quadraticReal (⟨1, -1⟩ : Zsqrtd 2) = 1 - Real.sqrt 2 := by
      rw [g64a_qr]; norm_num; try ring
    have e2 : quadraticReal (star (⟨1, -1⟩ : Zsqrtd 2)) = 1 + Real.sqrt 2 := by
      rw [g64a_qrs]; norm_num; try ring
    rw [g64a_mem, star_mul', map_mul, map_mul, e1, e2]
    generalize quadraticReal c = p at *
    generalize quadraticReal (star c) = q at *
    have hy0 : y0 / (1 + Real.sqrt 2) * (1 + Real.sqrt 2) = y0 := div_mul_cancel₀ _ hμ.ne'
    generalize y0 / (1 + Real.sqrt 2) = Y at *
    have m1 := mul_lt_mul_of_pos_left b3 hμ
    have m2 := mul_le_mul_of_nonneg_left b4 hμ.le
    have hs1 : (0:ℝ) ≤ Real.sqrt 2 - 1 := by linarith
    have m3 := mul_le_mul_of_nonneg_left b2 hs1
    have m4 := mul_le_mul_of_nonneg_left b1.le hs1
    have k3 : (Real.sqrt 2 - 1) * (-(1 + Real.sqrt 2) * (x0 + 1) + 1 + Real.sqrt 2) = -x0 := by
      linear_combination (-x0) * hs
    have k4 : (Real.sqrt 2 - 1) * (-(1 + Real.sqrt 2) * (x0 + 1)) = -(x0 + 1) := by
      linear_combination (-(x0 + 1)) * hs
    have k1 : (1 + Real.sqrt 2) * Y = y0 := by linear_combination hy0
    have k2 : (1 + Real.sqrt 2) * (Y + Real.sqrt 2) = y0 + Real.sqrt 2 + 2 := by
      linear_combination hy0 + hs
    have k5 : (1 - Real.sqrt 2) * p = -((Real.sqrt 2 - 1) * p) := by ring
    rw [k5]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith

theorem g64a_mu_pos : 0 < scaleUnit := by
  rw [scaleUnit]; have := Real.sqrt_nonneg 2; linarith

theorem g64a_mu_gt : 2 < scaleUnit := by
  rw [scaleUnit]; have := g64a_s2.1; linarith

theorem g64a_expand_sol (x0 x1 y0 y1 : ℝ) (a : Zsqrtd 2)
    (ha : a ∈ rectangleSolutions (scaleUnit * x0) (scaleUnit * x1) (-y1 / scaleUnit) (-y0 / scaleUnit)) :
    (smallUnit : Zsqrtd 2) * a ∈ rectangleSolutions x0 x1 y0 y1 := by
  obtain ⟨s1, s2⟩ := g64a_s2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hμ := g64a_mu_pos
  rw [g64a_mem] at ha ⊢
  rw [star_mul', map_mul, map_mul]
  have e1 : quadraticReal (smallUnit : Zsqrtd 2) = Real.sqrt 2 - 1 := by
    rw [g64a_qr]; simp [smallUnit]; ring
  have e2 : quadraticReal (star (smallUnit : Zsqrtd 2)) = -scaleUnit := by
    rw [g64a_qrs]; simp [smallUnit, scaleUnit]; ring
  rw [e1, e2]
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := ha
  rw [le_div_iff₀ hμ] at a4
  rw [div_le_iff₀ hμ] at a3
  have hk : (Real.sqrt 2 - 1) * scaleUnit = 1 := by rw [scaleUnit]; nlinarith
  have hs1 : (0:ℝ) ≤ Real.sqrt 2 - 1 := by linarith
  have m1 := mul_le_mul_of_nonneg_left a1 hs1
  have m2 := mul_le_mul_of_nonneg_left a2 hs1
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have : (Real.sqrt 2 - 1) * (scaleUnit * x0) = x0 := by rw [← mul_assoc, hk, one_mul]
    linarith
  · have : (Real.sqrt 2 - 1) * (scaleUnit * x1) = x1 := by rw [← mul_assoc, hk, one_mul]
    linarith
  · linarith
  · linarith

theorem g64a_contract_sol (x0 x1 y0 y1 : ℝ) (a : Zsqrtd 2)
    (ha : a ∈ rectangleSolutions (x0 / scaleUnit) (x1 / scaleUnit) (-scaleUnit * y1) (-scaleUnit * y0)) :
    (((smallUnit⁻¹ : (Zsqrtd 2)ˣ) : Zsqrtd 2)) * a ∈ rectangleSolutions x0 x1 y0 y1 := by
  obtain ⟨s1, s2⟩ := g64a_s2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hμ := g64a_mu_pos
  rw [g64a_mem] at ha ⊢
  rw [star_mul', map_mul, map_mul]
  have hinv : (((smallUnit⁻¹ : (Zsqrtd 2)ˣ) : Zsqrtd 2)) = ⟨1, 1⟩ := rfl
  have e1 : quadraticReal (((smallUnit⁻¹ : (Zsqrtd 2)ˣ) : Zsqrtd 2)) = scaleUnit := by
    rw [hinv, g64a_qr, scaleUnit]; simp
  have e2 : quadraticReal (star (((smallUnit⁻¹ : (Zsqrtd 2)ˣ) : Zsqrtd 2))) = 1 - Real.sqrt 2 := by
    rw [hinv, g64a_qrs]; simp
  rw [e1, e2]
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := ha
  rw [div_le_iff₀ hμ] at a1
  rw [le_div_iff₀ hμ] at a2
  have hk : (Real.sqrt 2 - 1) * scaleUnit = 1 := by rw [scaleUnit]; nlinarith
  have hs1 : (0:ℝ) ≤ Real.sqrt 2 - 1 := by linarith
  have m3 := mul_le_mul_of_nonneg_left a3 hs1
  have m4 := mul_le_mul_of_nonneg_left a4 hs1
  have r3 : (Real.sqrt 2 - 1) * (-scaleUnit * y1) = -y1 := by
    rw [neg_mul, mul_neg, ← mul_assoc, hk, one_mul]
  have r4 : (Real.sqrt 2 - 1) * (-scaleUnit * y0) = -y0 := by
    rw [neg_mul, mul_neg, ← mul_assoc, hk, one_mul]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linarith
  · linarith
  · nlinarith
  · nlinarith

theorem g64a_runA (n : ℕ) : ∀ x0 x1 y0 y1 : ℝ, x0 < x1 →
    scaleUnit ^ 2 ≤ (x1 - x0) * (y1 - y0) → x1 - x0 ≤ scaleUnit →
    1 < scaleUnit ^ n * (x1 - x0) →
    ∃ a : Zsqrtd 2, ∃ cost : ℕ, RectangleRun x0 x1 y0 y1 a cost ∧
      a ∈ rectangleSolutions x0 x1 y0 y1 ∧ cost ≤ 50 + 20 * n := by
  have hμ := g64a_mu_pos
  have hμ2 := g64a_mu_gt
  induction n with
  | zero =>
    intro x0 x1 y0 y1 hx hA hle hlo
    rw [pow_zero, one_mul] at hlo
    exact ⟨_, _, RectangleRun.base hlo hle, g64a_norm x0 x1 y0 y1 hlo hle hA, le_refl _⟩
  | succ n ih =>
    intro x0 x1 y0 y1 hx hA hle hlo
    by_cases h1 : 1 < x1 - x0
    · exact ⟨_, _, RectangleRun.base h1 hle, g64a_norm x0 x1 y0 y1 h1 hle hA, by omega⟩
    · push Not at h1
      obtain ⟨a, c, hr, hs, hc⟩ := ih (scaleUnit * x0) (scaleUnit * x1) (-y1 / scaleUnit)
        (-y0 / scaleUnit) (by nlinarith)
        (by
          have : (scaleUnit * x1 - scaleUnit * x0) * (-y0 / scaleUnit - -y1 / scaleUnit) =
              (x1 - x0) * (y1 - y0) := by field_simp; ring
          rw [this]; exact hA)
        (by nlinarith)
        (by rw [pow_succ] at hlo; nlinarith)
      exact ⟨_, _, RectangleRun.expand h1 hr, g64a_expand_sol x0 x1 y0 y1 a hs, by omega⟩

theorem g64a_runB (n : ℕ) : ∀ x0 x1 y0 y1 : ℝ, x0 < x1 →
    scaleUnit ^ 2 ≤ (x1 - x0) * (y1 - y0) → 1 < x1 - x0 →
    x1 - x0 ≤ scaleUnit ^ (n + 1) →
    ∃ a : Zsqrtd 2, ∃ cost : ℕ, RectangleRun x0 x1 y0 y1 a cost ∧
      a ∈ rectangleSolutions x0 x1 y0 y1 ∧ cost ≤ 50 + 20 * n := by
  have hμ := g64a_mu_pos
  have hμ2 := g64a_mu_gt
  induction n with
  | zero =>
    intro x0 x1 y0 y1 hx hA hlo hle
    rw [zero_add, pow_one] at hle
    exact ⟨_, _, RectangleRun.base hlo hle, g64a_norm x0 x1 y0 y1 hlo hle hA, le_refl _⟩
  | succ n ih =>
    intro x0 x1 y0 y1 hx hA hlo hle
    by_cases h1 : x1 - x0 ≤ scaleUnit
    · exact ⟨_, _, RectangleRun.base hlo h1, g64a_norm x0 x1 y0 y1 hlo h1 hA, by omega⟩
    · push Not at h1
      have e : x1 / scaleUnit - x0 / scaleUnit = (x1 - x0) / scaleUnit := by ring
      obtain ⟨a, c, hr, hs, hc⟩ := ih (x0 / scaleUnit) (x1 / scaleUnit) (-scaleUnit * y1)
        (-scaleUnit * y0) (by rw [div_lt_div_iff_of_pos_right hμ]; exact hx)
        (by
          have : (x1 / scaleUnit - x0 / scaleUnit) * (-scaleUnit * y0 - -scaleUnit * y1) =
              (x1 - x0) * (y1 - y0) := by field_simp; ring
          rw [this]; exact hA)
        (by rw [e, lt_div_iff₀ hμ]; linarith)
        (by rw [e, div_le_iff₀ hμ, ← pow_succ]; exact hle)
      exact ⟨_, _, RectangleRun.contract h1 hr, g64a_contract_sol x0 x1 y0 y1 a hs, by omega⟩

theorem g64a_construct :
    ∃ C : ℝ, 0 < C ∧ ∀ x0 x1 y0 y1 : ℝ,
      x0 < x1 → y0 < y1 →
      (1 + Real.sqrt 2) ^ 2 ≤ (x1 - x0) * (y1 - y0) →
      ∃ a : Zsqrtd 2, ∃ cost : ℕ,
        RectangleRun x0 x1 y0 y1 a cost ∧ a ∈ rectangleSolutions x0 x1 y0 y1 ∧
        (cost : ℝ) ≤ C * (1 + |Real.log (x1 - x0)|) ^ 2 := by
  refine ⟨70, by norm_num, fun x0 x1 y0 y1 hx hy hA => ?_⟩
  have hμ := g64a_mu_pos
  have hμ2 := g64a_mu_gt
  have hA' : scaleUnit ^ 2 ≤ (x1 - x0) * (y1 - y0) := hA
  set δ := x1 - x0 with hδ
  have hδ0 : 0 < δ := by linarith
  set L := |Real.log δ|
  have hL0 : 0 ≤ L := abs_nonneg _
  have hlμ : 0.69 < Real.log scaleUnit := by
    have := Real.log_two_gt_d9
    have := Real.log_lt_log (by norm_num) hμ2
    linarith
  set n : ℕ := ⌊L / Real.log scaleUnit⌋₊ + 1 with hn
  have hn1 : L / Real.log scaleUnit < n := by
    rw [hn]; push_cast; exact Nat.lt_floor_add_one _
  have hn2 : (n : ℝ) ≤ L / Real.log scaleUnit + 1 := by
    rw [hn]; push_cast; linarith [Nat.floor_le (div_nonneg hL0 (by linarith : (0:ℝ) ≤ Real.log scaleUnit))]
  have hpow : scaleUnit ^ n = Real.exp (n * Real.log scaleUnit) := by
    rw [Real.exp_nat_mul, Real.exp_log hμ]
  have hnl : L < n * Real.log scaleUnit := by
    rwa [div_lt_iff₀ (by linarith)] at hn1
  have hbig : Real.exp L < scaleUnit ^ n := by rw [hpow]; exact Real.exp_lt_exp.2 hnl
  have hd1 : δ ≤ Real.exp L := by
    calc δ = Real.exp (Real.log δ) := (Real.exp_log hδ0).symm
      _ ≤ Real.exp L := Real.exp_le_exp.2 (le_abs_self _)
  have hd2 : δ⁻¹ ≤ Real.exp L := by
    calc δ⁻¹ = Real.exp (-Real.log δ) := by rw [Real.exp_neg, Real.exp_log hδ0]
      _ ≤ Real.exp L := Real.exp_le_exp.2 (neg_le_abs _)
  have hcost : ((50 + 20 * n : ℕ) : ℝ) ≤ 70 * (1 + L) ^ 2 := by
    push_cast
    have : (n : ℝ) ≤ 1 + 29 / 20 * L := by
      have : L / Real.log scaleUnit ≤ 29 / 20 * L := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    nlinarith
  by_cases hc : δ ≤ scaleUnit
  · obtain ⟨a, c, hr, hs, hcc⟩ := g64a_runA n x0 x1 y0 y1 hx hA' hc (by
      have := mul_lt_mul_of_pos_right (lt_of_le_of_lt hd2 hbig) hδ0
      rwa [inv_mul_cancel₀ hδ0.ne'] at this)
    refine ⟨a, c, hr, hs, le_trans ?_ hcost⟩
    exact_mod_cast hcc
  · push Not at hc
    obtain ⟨a, c, hr, hs, hcc⟩ := g64a_runB n x0 x1 y0 y1 hx hA' (by linarith) (by
      rw [pow_succ]; nlinarith)
    refine ⟨a, c, hr, hs, le_trans ?_ hcost⟩
    exact_mod_cast hcc

theorem g64a_evenLift (b : Zsqrtd 2) :
    quadraticReal (evenLift b) = Real.sqrt 2 * quadraticReal b ∧
    quadraticReal (star (evenLift b)) = -(Real.sqrt 2 * quadraticReal (star b)) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  constructor
  · rw [g64a_qr, g64a_qr]; simp only [evenLift]; push_cast
    linear_combination (-(b.im : ℝ)) * hs
  · rw [g64a_qrs, g64a_qrs]; simp only [evenLift]; push_cast
    linear_combination (-(b.im : ℝ)) * hs

theorem g64a_parity :
    ∃ C : ℝ, 0 < C ∧ ∀ x0 x1 y0 y1 : ℝ,
      x0 < x1 → y0 < y1 →
      2 * (1 + Real.sqrt 2) ^ 2 ≤ (x1 - x0) * (y1 - y0) →
      ∃ ae ao : Zsqrtd 2, ∃ cost : ℕ,
        ParityRun x0 x1 y0 y1 ae ao cost ∧
        ae ∈ rectangleSolutions x0 x1 y0 y1 ∧ Even ae.re ∧
        ao ∈ rectangleSolutions x0 x1 y0 y1 ∧ Odd ao.re ∧
        (cost : ℝ) ≤ C * (1 + |Real.log (x1 - x0)|) ^ 2 := by
  obtain ⟨C, hC, hcon⟩ := g64a_construct
  refine ⟨4 * C * 4 + 30, by positivity, fun x0 x1 y0 y1 hx hy hA => ?_⟩
  obtain ⟨s1, s2⟩ := g64a_s2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hr : 0 < Real.sqrt 2 := by linarith
  have hw : ∀ u v : ℝ, (v / Real.sqrt 2 - u / Real.sqrt 2) = (v - u) / Real.sqrt 2 := by
    intro u v; ring
  have hlog : |Real.log ((x1 - x0) / Real.sqrt 2)| ≤ |Real.log (x1 - x0)| + 1 := by
    rw [Real.log_div (by linarith) hr.ne']
    have h1 : 0 < Real.log (Real.sqrt 2) := Real.log_pos (by linarith)
    have h2 : Real.log (Real.sqrt 2) < 1 := by
      have := Real.log_le_sub_one_of_pos hr; linarith
    calc |Real.log (x1 - x0) - Real.log (Real.sqrt 2)| ≤
        |Real.log (x1 - x0)| + |Real.log (Real.sqrt 2)| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_pos h1]; linarith
  have harea : ∀ u0 u1 v0 v1 : ℝ, (u1 - u0) * (v1 - v0) = (x1 - x0) * (y1 - y0) →
      (1 + Real.sqrt 2) ^ 2 ≤ (u1 / Real.sqrt 2 - u0 / Real.sqrt 2) *
        (-v0 / Real.sqrt 2 - -v1 / Real.sqrt 2) := by
    intro u0 u1 v0 v1 he
    have : (u1 / Real.sqrt 2 - u0 / Real.sqrt 2) * (-v0 / Real.sqrt 2 - -v1 / Real.sqrt 2) =
        (x1 - x0) * (y1 - y0) / 2 := by
      rw [← he]; field_simp; rw [hs]; ring
    rw [this]; linarith
  obtain ⟨be, ce, hre, hse, hce⟩ := hcon (x0 / Real.sqrt 2) (x1 / Real.sqrt 2)
    (-y1 / Real.sqrt 2) (-y0 / Real.sqrt 2)
    (by rw [div_lt_div_iff_of_pos_right hr]; exact hx)
    (by rw [div_lt_div_iff_of_pos_right hr]; linarith)
    (harea x0 x1 y0 y1 rfl)
  obtain ⟨bo, co, hro, hso, hco⟩ := hcon ((x0 - 1) / Real.sqrt 2) ((x1 - 1) / Real.sqrt 2)
    (-(y1 - 1) / Real.sqrt 2) (-(y0 - 1) / Real.sqrt 2)
    (by rw [div_lt_div_iff_of_pos_right hr]; linarith)
    (by rw [div_lt_div_iff_of_pos_right hr]; linarith)
    (harea (x0 - 1) (x1 - 1) (y0 - 1) (y1 - 1) (by ring))
  refine ⟨evenLift be, evenLift bo + 1, ce + co + 30, ⟨be, bo, ce, co, hre, hro, rfl, rfl, rfl⟩,
    ?_, ⟨be.im, by simp [evenLift]; ring⟩, ?_, ⟨bo.im, by simp [evenLift]⟩, ?_⟩
  · obtain ⟨e1, e2⟩ := g64a_evenLift be
    rw [g64a_mem] at hse ⊢
    rw [e1, e2]
    obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hse
    rw [le_div_iff₀ hr] at a2 a4
    rw [div_le_iff₀ hr] at a1 a3
    refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  · obtain ⟨e1, e2⟩ := g64a_evenLift bo
    rw [g64a_mem] at hso ⊢
    rw [star_add, star_one, map_add, map_add, map_one, e1, e2]
    obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hso
    rw [le_div_iff₀ hr] at a2 a4
    rw [div_le_iff₀ hr] at a1 a3
    refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  · have w1 := hw x0 x1
    have w2 := hw (x0 - 1) (x1 - 1)
    rw [w1] at hce
    rw [w2, show x1 - 1 - (x0 - 1) = x1 - x0 by ring] at hco
    set L := |Real.log (x1 - x0)|
    have hL : 0 ≤ L := abs_nonneg _
    have k1 : (1 + |Real.log ((x1 - x0) / Real.sqrt 2)|) ^ 2 ≤ 4 * (1 + L) ^ 2 := by
      have h0 := abs_nonneg (Real.log ((x1 - x0) / Real.sqrt 2))
      nlinarith
    push_cast
    nlinarith

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ x0 x1 y0 y1 : ℝ,
      x0 < x1 → y0 < y1 →
      (1 + Real.sqrt 2) ^ 2 ≤ (x1 - x0) * (y1 - y0) →
      ∃ a : Zsqrtd 2, ∃ cost : ℕ,
        RectangleRun x0 x1 y0 y1 a cost ∧ a ∈ rectangleSolutions x0 x1 y0 y1 ∧
        (cost : ℝ) ≤ C * (1 + |Real.log (x1 - x0)|) ^ 2 :=
  g64a_construct
