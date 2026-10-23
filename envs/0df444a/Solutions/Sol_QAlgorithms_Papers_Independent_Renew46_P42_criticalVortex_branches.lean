-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.criticalVortex_branches
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:56:14.304553+00:00
-- url     : https://prove2.me/submissions/f36f0063-9630-4d88-918b-c2618b49bb26

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open Filter Set

lemma x6_cs_scale (c n : ℝ) (i : Fin 3) : criticalSpeed c n i = c * criticalSpeed 1 n i := by
  unfold criticalSpeed; ring

/-- A cubic with three distinct roots factors. -/
lemma x6_cubic_factor (a b c d r0 r1 r2 : ℝ) (h0 : a*r0^3+b*r0^2+c*r0+d=0)
    (h1 : a*r1^3+b*r1^2+c*r1+d=0) (h2 : a*r2^3+b*r2^2+c*r2+d=0)
    (d01 : r0 ≠ r1) (d02 : r0 ≠ r2) (d12 : r1 ≠ r2) (x : ℝ) :
    a*x^3+b*x^2+c*x+d = a*(x-r0)*(x-r1)*(x-r2) := by
  have hQ1 : a*(r1^2+r1*r0+r0^2)+b*(r1+r0)+c = 0 := by
    have : (r1 - r0) * (a*(r1^2+r1*r0+r0^2)+b*(r1+r0)+c) = 0 := by linear_combination h1 - h0
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h).symm d01
    · exact h
  have hQ2 : a*(r2^2+r2*r0+r0^2)+b*(r2+r0)+c = 0 := by
    have : (r2 - r0) * (a*(r2^2+r2*r0+r0^2)+b*(r2+r0)+c) = 0 := by linear_combination h2 - h0
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h).symm d02
    · exact h
  have hS : a*(r0+r1+r2)+b = 0 := by
    have : (r2 - r1) * (a*(r0+r1+r2)+b) = 0 := by linear_combination hQ2 - hQ1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h).symm d12
    · exact h
  linear_combination (x^2 - (r0+r1)*x - r0^2 + r0*(r0+r1)) * hS + (x - r0) * hQ1 + h0

lemma x6_root (n s C : ℝ) (hn : 1 < n) (hs : s ^ 2 = 6 * n ^ 2 - 5) (hspos : 0 < s)
    (hC : 4 * C ^ 3 - 3 * C =
      -(27 - 70 * n ^ 2 + 45 * n ^ 4) / (2 * n ^ 2 * (6 * n ^ 2 - 5) * s)) :
    criticalCubic n ((2 * n * 1 * s * C - n * 1) / (3 * (n ^ 2 - 1))) = 0 := by
  have ha : n ^ 2 - 1 ≠ 0 := by nlinarith
  have hn0 : 0 < n := by linarith
  have hD : 0 < 6 * n ^ 2 - 5 := by nlinarith
  have hy' : (-(27 - 70 * n ^ 2 + 45 * n ^ 4) / (2 * n ^ 2 * (6 * n ^ 2 - 5) * s)) *
      (2 * n ^ 2 * (6 * n ^ 2 - 5) * s) = -(27 - 70 * n ^ 2 + 45 * n ^ 4) :=
    div_mul_cancel₀ _ (by positivity)
  rw [← hC] at hy'
  have e : criticalCubic n ((2 * n * 1 * s * C - n * 1) / (3 * (n ^ 2 - 1))) =
      (8 * n ^ 3 * s ^ 3 * C ^ 3 - 6 * n ^ 3 * (6 * n ^ 2 - 5) * s * C +
        n * (27 - 70 * n ^ 2 + 45 * n ^ 4)) / (27 * (n ^ 2 - 1) ^ 2) := by
    unfold criticalCubic; field_simp; ring
  rw [e, div_eq_zero_iff]; left
  linear_combination (8 * n ^ 3 * s * C ^ 3) * hs + n * hy'

lemma x6_signs (X0 X1 X2 : ℝ) (o02 : X2 < X0) (o21 : X1 < X2) (p0 : X0 * X1 * X2 < 0)
    (p1 : (1 - X0) * (1 - X1) * (1 - X2) < 0) : X1 < 0 ∧ 0 < X2 ∧ X2 < 1 ∧ 1 < X0 := by
  have s1 : X1 < 0 := by
    by_contra h; push Not at h
    have : 0 ≤ X0 * X1 * X2 := by
      have : 0 ≤ X2 := by linarith
      have : 0 ≤ X0 := by linarith
      positivity
    linarith
  have s0 : 1 < X0 := by
    by_contra h; push Not at h
    have : 0 ≤ (1 - X0) * (1 - X1) * (1 - X2) := by
      apply mul_nonneg (mul_nonneg _ _) _ <;> linarith
    linarith
  have s2 : 0 < X2 := by
    by_contra h; push Not at h
    have h12 : 0 ≤ X1 * X2 := mul_nonneg_of_nonpos_of_nonpos s1.le h
    have : 0 ≤ X0 * (X1 * X2) := mul_nonneg (by linarith) h12
    linarith [mul_assoc X0 X1 X2]
  have s2' : X2 < 1 := by
    by_contra h; push Not at h
    have h02 : 0 ≤ (1 - X0) * (1 - X2) := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have : 0 ≤ (1 - X1) * ((1 - X0) * (1 - X2)) := mul_nonneg (by linarith) h02
    nlinarith
  exact ⟨s1, s2, s2', s0⟩

lemma x6_hasDerivAt_u (c W r : ℝ) (hc : 0 < c) (hW : 0 < W) (hr : 0 < r) :
    HasDerivAt (vortexSpeed c W)
      (-(vortexSpeed c W r) * (c ^ 2 - (vortexSpeed c W r) ^ 2) / (c ^ 2 * r)) r := by
  have hg0 : 0 < 1 + W ^ 2 / (c ^ 2 * r ^ 2) := by positivity
  have hq : HasDerivAt (fun r : ℝ => c ^ 2 * r ^ 2) (c ^ 2 * (2 * r)) r := by
    have := (hasDerivAt_pow 2 r).const_mul (c ^ 2)
    simpa using this
  have hg := ((hasDerivAt_const r (W ^ 2)).div hq (by positivity)).const_add 1
  have hγ := hg.sqrt (by simpa using hg0.ne')
  have hγr := hγ.mul (hasDerivAt_id r)
  have hu := (hasDerivAt_const r W).div hγr (by simp only [Pi.mul_apply, Pi.div_apply, id]; positivity)
  have hfun : ((fun _ : ℝ => W) / ((fun y => Real.sqrt (1 + ((fun _ : ℝ => W ^ 2) /
      fun r : ℝ => c ^ 2 * r ^ 2) y)) * id)) = vortexSpeed c W := by
    funext x; simp [vortexSpeed, vortexGamma]
  rw [hfun] at hu
  refine hu.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.div_apply, id]
  set g := 1 + W ^ 2 / (c ^ 2 * r ^ 2) with hg_def
  have hsq : Real.sqrt g ^ 2 = g := Real.sq_sqrt hg0.le
  have hsp : 0 < Real.sqrt g := Real.sqrt_pos.2 hg0
  have hv : vortexSpeed c W r = W / (Real.sqrt g * r) := by simp [vortexSpeed, vortexGamma, hg_def]
  rw [hv]
  field_simp
  ring

lemma x6_deriv (c n W r : ℝ) (hc : 0 < c) (hW : 0 < W) (hr : 0 < r)
    (hne : n * vortexSpeed c W r ≠ c) :
    deriv (turningBranch c n (vortexSpeed c W) (-1)) r = 0 ↔
      criticalCubic n (vortexSpeed c W r / c) = 0 := by
  have hu := x6_hasDerivAt_u c W r hc hW hr
  set u := vortexSpeed c W with hu_def
  have hden : n * u r + (-1) * c ≠ 0 := by
    intro h; apply hne; linarith
  have hR := ((hasDerivAt_id r).mul ((hasDerivAt_const r (n * c)).add (hu.const_mul (-1)))).div
    ((hu.const_mul n).add (hasDerivAt_const r ((-1) * c))) (by simpa using hden)
  rw [show turningBranch c n u (-1) = id * ((fun _ => n * c) + fun y => -1 * u y) /
      ((fun y => n * u y) + fun _ => -1 * c) from by funext x; simp [turningBranch], hR.deriv]
  simp only [Pi.add_apply, Pi.mul_apply, id]
  have hc0 : c ≠ 0 := hc.ne'
  have key : ((1 * (n * c + -1 * u r) + r * (0 + -1 * (-u r * (c ^ 2 - u r ^ 2) / (c ^ 2 * r)))) *
          (n * u r + -1 * c) -
        r * (n * c + -1 * u r) * (n * (-u r * (c ^ 2 - u r ^ 2) / (c ^ 2 * r)) + 0)) /
      (n * u r + -1 * c) ^ 2 = -(criticalCubic n (u r / c)) * c ^ 2 / (n * u r + -1 * c) ^ 2 := by
    congr 1
    unfold criticalCubic
    field_simp
    ring
  rw [key, div_eq_zero_iff, mul_eq_zero, neg_eq_zero]
  have h1 : (n * u r + -1 * c) ^ 2 ≠ 0 := pow_ne_zero _ hden
  have h2 : c ^ 2 ≠ 0 := pow_ne_zero _ hc0
  tauto

lemma x6_core (n : ℝ) (hn : 1 < n) :
    (∀ i : Fin 3, criticalCubic n (criticalSpeed 1 n i) = 0) ∧
    criticalSpeed 1 n 1 < 0 ∧ 0 < criticalSpeed 1 n 2 ∧ criticalSpeed 1 n 2 < 1 ∧
    1 < criticalSpeed 1 n 0 ∧
    ∀ x, criticalCubic n x = (n ^ 2 - 1) * (x - criticalSpeed 1 n 0) *
      (x - criticalSpeed 1 n 1) * (x - criticalSpeed 1 n 2) := by
  have hn0 : 0 < n := by linarith
  have ha : 0 < n ^ 2 - 1 := by nlinarith
  have hD : 0 < 6 * n ^ 2 - 5 := by nlinarith
  obtain ⟨s, hs_eq⟩ : ∃ s, s = Real.sqrt (6 * n ^ 2 - 5) := ⟨_, rfl⟩
  have hs : s ^ 2 = 6 * n ^ 2 - 5 := by rw [hs_eq]; exact Real.sq_sqrt hD.le
  have hspos : 0 < s := by rw [hs_eq]; exact Real.sqrt_pos.2 hD
  obtain ⟨y, hy_eq⟩ : ∃ y, y = -(27 - 70 * n ^ 2 + 45 * n ^ 4) / (2 * n ^ 2 * (6 * n ^ 2 - 5) * s) :=
    ⟨_, rfl⟩
  have hy2 : y ^ 2 < 1 := by
    rw [hy_eq, div_pow, div_lt_one (by positivity)]
    have e1 : (2 * n ^ 2 * (6 * n ^ 2 - 5) * s) ^ 2 = 4 * n ^ 4 * (6 * n ^ 2 - 5) ^ 3 := by
      rw [mul_pow, hs]; ring
    have e2 : 4 * n ^ 4 * (6 * n ^ 2 - 5) ^ 3 - (-(27 - 70 * n ^ 2 + 45 * n ^ 4)) ^ 2 =
        27 * (n ^ 2 - 1) ^ 4 * (32 * n ^ 2 - 27) := by ring
    have : 0 < 27 * (n ^ 2 - 1) ^ 4 * (32 * n ^ 2 - 27) := by
      have : 0 < 32 * n ^ 2 - 27 := by nlinarith
      positivity
    rw [e1]; linarith
  have hyab : |y| < 1 := by rwa [sq_lt_one_iff_abs_lt_one] at hy2
  have hy1 : -1 < y := (abs_lt.1 hyab).1
  have hy1' : y < 1 := (abs_lt.1 hyab).2
  have hbeta : criticalBeta n = Real.arccos y := by
    rw [criticalBeta, hy_eq, hs_eq]
  set β := criticalBeta n with hβ
  have hcosβ : Real.cos β = y := by rw [hbeta]; exact Real.cos_arccos hy1.le hy1'.le
  have hβ0 : 0 < β := by rw [hbeta]; exact Real.arccos_pos.2 hy1'
  have hβπ : β < Real.pi := by rw [hbeta]; exact Real.arccos_lt_pi.2 hy1
  have hcube : ∀ k : ℕ, 4 * Real.cos ((2 * Real.pi * (k : ℝ) + β) / 3) ^ 3 -
      3 * Real.cos ((2 * Real.pi * (k : ℝ) + β) / 3) = y := by
    intro k
    rw [← Real.cos_three_mul]
    have : 3 * ((2 * Real.pi * (k : ℝ) + β) / 3) = β + k * (2 * Real.pi) := by ring
    rw [this, Real.cos_add_nat_mul_two_pi, hcosβ]
  have hX : ∀ i : Fin 3, criticalSpeed 1 n i =
      (2 * n * 1 * s * Real.cos ((2 * Real.pi * ((i.val : ℕ) : ℝ) + β) / 3) - n * 1) /
        (3 * (n ^ 2 - 1)) := by
    intro i; rw [criticalSpeed, hs_eq]
  have hroot : ∀ i : Fin 3, criticalCubic n (criticalSpeed 1 n i) = 0 := by
    intro i; rw [hX i]
    exact x6_root n s _ hn hs hspos (by rw [hcube, hy_eq])
  -- ordering of the cosines
  have hX0 : criticalSpeed 1 n 0 = (2 * n * 1 * s * Real.cos (β / 3) - n * 1) / (3 * (n ^ 2 - 1)) := by
    rw [hX 0]; congr 3; simp
  have hX1 : criticalSpeed 1 n 1 =
      (2 * n * 1 * s * Real.cos ((2 * Real.pi + β) / 3) - n * 1) / (3 * (n ^ 2 - 1)) := by
    rw [hX 1]; congr 3; simp
  have hX2 : criticalSpeed 1 n 2 =
      (2 * n * 1 * s * Real.cos ((2 * Real.pi - β) / 3) - n * 1) / (3 * (n ^ 2 - 1)) := by
    rw [hX 2]; congr 3
    have : (2 * Real.pi * (((2 : Fin 3).val : ℕ) : ℝ) + β) / 3 = 2 * Real.pi - (2 * Real.pi - β) / 3 := by
      simp; ring
    rw [this, Real.cos_two_pi_sub]
  have hpi := Real.pi_pos
  have c02 : Real.cos ((2 * Real.pi - β) / 3) < Real.cos (β / 3) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have c21 : Real.cos ((2 * Real.pi + β) / 3) < Real.cos ((2 * Real.pi - β) / 3) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have hk : 0 < 2 * n * 1 * s := by positivity
  have h3a : 0 < 3 * (n ^ 2 - 1) := by positivity
  have o02 : criticalSpeed 1 n 2 < criticalSpeed 1 n 0 := by
    rw [hX0, hX2]; apply div_lt_div_of_pos_right _ h3a; nlinarith
  have o21 : criticalSpeed 1 n 1 < criticalSpeed 1 n 2 := by
    rw [hX1, hX2]; apply div_lt_div_of_pos_right _ h3a; nlinarith
  have hfac : ∀ x, criticalCubic n x = (n ^ 2 - 1) * (x - criticalSpeed 1 n 0) *
      (x - criticalSpeed 1 n 1) * (x - criticalSpeed 1 n 2) := by
    intro x
    have h := fun i => hroot i
    unfold criticalCubic at h ⊢
    have := x6_cubic_factor (n ^ 2 - 1) n (-2 * n ^ 2) n (criticalSpeed 1 n 0) (criticalSpeed 1 n 1)
      (criticalSpeed 1 n 2) (by linear_combination h 0) (by linear_combination h 1)
      (by linear_combination h 2) (by linarith) (by linarith) (by linarith) x
    linear_combination this
  set X0 := criticalSpeed 1 n 0
  set X1 := criticalSpeed 1 n 1
  set X2 := criticalSpeed 1 n 2
  have f0 := hfac 0
  have f1 := hfac 1
  have v0 : criticalCubic n 0 = n := by unfold criticalCubic; ring
  have v1 : criticalCubic n 1 = -(n - 1) ^ 2 := by unfold criticalCubic; ring
  rw [v0] at f0; rw [v1] at f1
  have p0 : X0 * X1 * X2 < 0 := by nlinarith
  have p1 : (1 - X0) * (1 - X1) * (1 - X2) < 0 := by
    have : 0 < (n - 1) ^ 2 := by nlinarith
    nlinarith
  obtain ⟨s1, s2, s2', s0⟩ := x6_signs X0 X1 X2 o02 o21 p0 p1
  exact ⟨hroot, s1, s2, s2', s0, hfac⟩

lemma x6_anti (n m : ℝ) (hn : 1 < n) (hnm : n < m) :
    criticalSpeed 1 m 2 < criticalSpeed 1 n 2 := by
  obtain ⟨hr, -, s2, s2', -, -⟩ := x6_core n hn
  obtain ⟨-, t1, -, -, t0, hfm⟩ := x6_core m (by linarith)
  set x := criticalSpeed 1 n 2
  have h0 := hr 2
  have hid : n * criticalCubic m x = (m - n) * (x * (x ^ 2 * (n * m + 1) - 2 * n * m)) +
      m * criticalCubic n x := by unfold criticalCubic; ring
  rw [h0, mul_zero, add_zero] at hid
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hnm1 : n * m + 1 < 2 * n * m := by nlinarith
  have hneg : x ^ 2 * (n * m + 1) - 2 * n * m < 0 := by nlinarith
  have hfneg : criticalCubic m x < 0 := by
    have : (m - n) * (x * (x ^ 2 * (n * m + 1) - 2 * n * m)) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (mul_neg_of_pos_of_neg s2 hneg)
    have hn0 : 0 < n := by linarith
    by_contra h; push Not at h
    nlinarith
  rw [hfm x] at hfneg
  by_contra h; push Not at h
  have ha : 0 < m ^ 2 - 1 := by nlinarith
  have hA : (m ^ 2 - 1) * (x - criticalSpeed 1 m 0) * (x - criticalSpeed 1 m 1) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha (by linarith)) (by linarith)
  have : 0 ≤ (m ^ 2 - 1) * (x - criticalSpeed 1 m 0) * (x - criticalSpeed 1 m 1) *
      (x - criticalSpeed 1 m 2) := mul_nonneg_of_nonpos_of_nonpos hA.le (by linarith)
  linarith

end

end QAlgorithms.Papers.Independent.Renew46.P42

open QAlgorithms.Papers.Independent.Renew46.P42 Set

theorem solution (c : ℝ) (hc : 0 < c) :
    (∀ n : ℝ, 1 < n →
      (∀ i : Fin 3, criticalCubic n (criticalSpeed c n i / c) = 0) ∧
      (∀ xi : ℝ, criticalCubic n xi = 0 ↔ ∃ i : Fin 3, xi = criticalSpeed c n i / c) ∧
      c < criticalSpeed c n 0 ∧ criticalSpeed c n 1 < 0 ∧
      0 < criticalSpeed c n 2 ∧ criticalSpeed c n 2 < c ∧
      (∀ v : ℝ, (criticalCubic n (v / c) = 0 ∧ 0 ≤ v ∧ v < c) ↔
        v = criticalSpeed c n 2)) ∧
    StrictAntiOn (fun n => criticalSpeed c n 2) (Ioi 1) ∧
    (∀ (n W r : ℝ), 1 < n → 0 < W → 0 < r →
      n * vortexSpeed c W r ≠ c →
      (deriv (turningBranch c n (vortexSpeed c W) (-1)) r = 0 ↔
        criticalCubic n (vortexSpeed c W r / c) = 0)) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hdiv : ∀ n (i : Fin 3), criticalSpeed c n i / c = criticalSpeed 1 n i := by
    intro n i; rw [x6_cs_scale, mul_div_cancel_left₀ _ hc0]
  refine ⟨fun n hn => ?_, ?_, fun n W r hn hW hr hne => x6_deriv c n W r hc hW hr hne⟩
  · obtain ⟨hr, s1, s2, s2', s0, hf⟩ := x6_core n hn
    have ha : 0 < n ^ 2 - 1 := by nlinarith
    simp only [hdiv]
    have hroots : ∀ xi : ℝ, criticalCubic n xi = 0 ↔ ∃ i : Fin 3, xi = criticalSpeed 1 n i := by
      intro xi; constructor
      · intro h
        rw [hf xi] at h
        rcases mul_eq_zero.1 h with h | h
        · rcases mul_eq_zero.1 h with h | h
          · rcases mul_eq_zero.1 h with h | h
            · exact absurd h ha.ne'
            · exact ⟨0, sub_eq_zero.1 h⟩
          · exact ⟨1, sub_eq_zero.1 h⟩
        · exact ⟨2, sub_eq_zero.1 h⟩
      · rintro ⟨i, rfl⟩; exact hr i
    refine ⟨hr, hroots, ?_, ?_, ?_, ?_, ?_⟩
    · rw [x6_cs_scale]; nlinarith
    · rw [x6_cs_scale]; nlinarith
    · rw [x6_cs_scale]; positivity
    · rw [x6_cs_scale]; nlinarith
    · intro v; constructor
      · rintro ⟨h, hv0, hvc⟩
        have hv0' : 0 ≤ v / c := div_nonneg hv0 hc.le
        have hvc' : v / c < 1 := (div_lt_one hc).2 hvc
        obtain ⟨i, hi⟩ := (hroots _).1 h
        fin_cases i
        · simp at hi; linarith
        · simp at hi; linarith
        · simp at hi
          rw [x6_cs_scale, ← hi]; field_simp
      · rintro rfl
        rw [hdiv]
        refine ⟨hr 2, ?_, ?_⟩ <;> rw [x6_cs_scale] <;> nlinarith
  · intro n hn m hm hnm
    simp only [mem_Ioi] at hn hm
    simp only
    rw [x6_cs_scale, x6_cs_scale c n]
    exact mul_lt_mul_of_pos_left (x6_anti n m hn hnm) hc

