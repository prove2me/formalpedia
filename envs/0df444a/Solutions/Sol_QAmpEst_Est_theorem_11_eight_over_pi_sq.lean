-- Prove2me | solution 1 for QAmpEst.Est.theorem_11_eight_over_pi_sq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:11:54.79554+00:00
-- url     : https://prove2.me/submissions/6831209d-7dc2-41de-b944-c973094b4d36

import Definitions.Def_QAmpEst_Est_Fourier
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
set_option autoImplicit false
open scoped Real ComplexConjugate
open QAmpEst.Est

private lemma fc_amplitude (M : ℕ) (_hM : M ≠ 0) (ω : ℝ) (x : Fin M) :
    (qftInv M).mulVec (stateS M ω) x =
      (∑ y : Fin M, Complex.exp (2 * π * Complex.I * ((ω - (x : ℕ) / M : ℝ) : ℂ) * (y : ℕ))) / M := by
  have hs : (Real.sqrt M : ℂ) ^ 2 = M := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg M)
  unfold qftInv stateS Matrix.mulVec dotProduct
  simp only [Matrix.star_apply]
  unfold ShorAlgorithms.Shared.fourierMatrix
  simp only [Complex.star_def, map_mul, map_inv₀, Complex.conj_ofReal,
    ← Complex.exp_conj, map_div₀, Complex.conj_I, map_natCast, map_ofNat]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [div_eq_mul_inv]
  rw [show (Real.sqrt M : ℂ)⁻¹ * Complex.exp
      (2 * (π : ℂ) * -Complex.I * (y : ℕ) * (x : ℕ) * (M : ℂ)⁻¹) *
      (Complex.exp (2 * π * Complex.I * (ω : ℂ) * (y : ℕ)) * (Real.sqrt M : ℂ)⁻¹) =
    (Complex.exp (2 * π * -Complex.I * (y : ℕ) * (x : ℕ) * (M : ℂ)⁻¹) *
      Complex.exp (2 * π * Complex.I * (ω : ℂ) * (y : ℕ))) * ((Real.sqrt M : ℂ)^2)⁻¹ by ring]
  rw [hs, ← Complex.exp_add]
  push_cast
  congr 2
  ring

private lemma fc_exp_norm (t : ℝ) :
    Complex.normSq (Complex.exp (2 * π * Complex.I * (t : ℂ)) - 1) =
      4 * Real.sin (π * t) ^ 2 := by
  rw [show 2 * (π : ℂ) * Complex.I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hc := Real.cos_two_mul (π * t)
  have ht := Real.sin_sq_add_cos_sq (2 * π * t)
  rw [show 2 * π * t = 2 * (π * t) by ring] at ht ⊢
  nlinarith [Real.sin_sq_add_cos_sq (π * t)]

private lemma fc_prob_lower (M : ℕ) (hM : M ≠ 0) (ω : ℝ) (x : Fin M) :
    Real.sin (π * (M * ω - (x : ℕ))) ^ 2 ≤
      phaseProb M ω x * (π * (M * ω - (x : ℕ))) ^ 2 := by
  let d : ℝ := ω - (x : ℕ) / M
  let r : ℂ := Complex.exp (2 * π * Complex.I * (d : ℂ))
  let s : ℂ := ∑ y ∈ Finset.range M, r ^ y
  have ha : (qftInv M).mulVec (stateS M ω) x = s / M := by
    rw [fc_amplitude M hM ω x]
    congr 1
    calc
      _ = ∑ y : Fin M, r ^ (y : ℕ) := by
        apply Finset.sum_congr rfl
        intro y hy
        dsimp [r, d]
        rw [← Complex.exp_nat_mul]
        congr 1
        ring
      _ = s := Fin.sum_univ_eq_sum_range (fun y : ℕ => r ^ y) M
  have hg : s * (r - 1) = r ^ M - 1 := by
    exact geom_sum_mul r M
  have hr : r ^ M = Complex.exp (2 * π * Complex.I * ((M * d : ℝ) : ℂ)) := by
    dsimp [r]
    rw [← Complex.exp_nat_mul]
    push_cast
    congr 1
    ring
  have hn := congrArg Complex.normSq hg
  rw [Complex.normSq_mul, hr, fc_exp_norm (M * d), fc_exp_norm d] at hn
  have hp : phaseProb M ω x = Complex.normSq s / (M : ℝ) ^ 2 := by
    simp only [phaseProb, ha, map_div₀, Complex.normSq_natCast, pow_two]
  have hb := Real.sin_sq_le_sq (x := π * d)
  have hsp := Complex.normSq_nonneg s
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have hd : M * d = M * ω - (x : ℕ) := by dsimp [d]; field_simp
  rw [← hd, hp]
  have he : Complex.normSq s / (M : ℝ)^2 * (π * (M * d))^2 =
      Complex.normSq s * (π * d)^2 := by field_simp
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hb hsp]

private lemma fc_sine_edge (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    8 * t ^ 2 ≤ Real.sin (π * t) ^ 2 := by
  have h := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 π by constructor <;> positivity)
    (show π / 4 ∈ Set.Icc 0 π by constructor <;> linarith [Real.pi_pos])
    (show 0 ≤ 1 - 4 * t by linarith) (show 0 ≤ 4 * t by positivity)
    (show 1 - 4 * t + 4 * t = 1 by ring)
  simp only [Real.sin_zero, Real.sin_pi_div_four, smul_eq_mul, mul_zero, zero_add] at h
  have he : 4 * t * (π / 4) = π * t := by ring
  rw [he] at h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hn : 0 ≤ 4 * t * (Real.sqrt 2 / 2) := by positivity
  have hsq := mul_self_le_mul_self hn h
  nlinarith [hs]

private lemma fc_sine_middle (t : ℝ) (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 2) :
    8 * t ^ 2 * (1 - t) ^ 2 ≤
      Real.sin (π * t) ^ 2 * (t ^ 2 + (1 - t) ^ 2) := by
  let u : ℝ := 1 / 2 - t
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 / 4 := by dsimp [u]; linarith
  have hu2 : u ^ 2 ≤ 1 / 16 := by nlinarith
  have hp : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hc : 1 - 5 * u ^ 2 ≤ Real.sin (π * t) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := π * u)
    have he : π * u = π / 2 - π * t := by dsimp [u]; ring
    rw [show Real.cos (π * u) = Real.sin (π * t) by rw [he, Real.cos_pi_div_two_sub]] at h
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg u)]
  have hsq : (1 - 5 * u ^ 2) ^ 2 ≤ Real.sin (π * t) ^ 2 := by
    exact pow_le_pow_left₀ (by nlinarith) hc 2
  have hpos : 0 ≤ u ^ 2 * (1 - 31 / 2 * u ^ 2 + 50 * (u ^ 2) ^ 2) := by
    apply mul_nonneg (sq_nonneg u)
    have : 0 ≤ 1 - 31 / 2 * u ^ 2 := by linarith
    positivity
  have hpoly : 8 * t ^ 2 * (1 - t) ^ 2 ≤
      (1 - 5 * u ^ 2) ^ 2 * (t ^ 2 + (1 - t) ^ 2) := by
    dsimp [u] at hpos ⊢
    nlinarith only [hpos]
  exact hpoly.trans (mul_le_mul_of_nonneg_right hsq (by positivity))

private lemma fc_sine_pair (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    8 * t ^ 2 * (1 - t) ^ 2 ≤
      Real.sin (π * t) ^ 2 * (t ^ 2 + (1 - t) ^ 2) := by
  wlog hth : t ≤ 1 / 2 generalizing t
  · have h := this (1 - t) (by linarith) (by linarith) (by linarith)
    have he : π * (1 - t) = π - π * t := by ring
    rw [he, Real.sin_pi_sub] at h
    convert h using 1 <;> ring
  by_cases he : t ≤ 1 / 4
  · calc
      8 * t ^ 2 * (1 - t) ^ 2 ≤ 8 * t ^ 2 * (t ^ 2 + (1 - t) ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg t]) (by positivity)
      _ ≤ Real.sin (π * t) ^ 2 * (t ^ 2 + (1 - t) ^ 2) :=
        mul_le_mul_of_nonneg_right (fc_sine_edge t ht0 he) (by positivity)
  · exact fc_sine_middle t (by linarith) hth

private lemma fc_prob_periodic (M : ℕ) (ω : ℝ) (x : Fin M) (k : ℤ) :
    phaseProb M (ω + k) x = phaseProb M ω x := by
  have hs : stateS M (ω + k) = stateS M ω := by
    funext y
    unfold stateS
    congr 1
    rw [show 2 * (π : ℂ) * Complex.I * ((ω + k : ℝ) : ℂ) * (y : ℕ) =
      2 * π * Complex.I * (ω : ℂ) * (y : ℕ) + ((k * (y : ℕ) : ℤ) : ℂ) * (2 * π * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [phaseProb, hs]

private lemma fc_dist_bound (M : ℕ) (hM : 0 < M) (ω : ℝ) (x : Fin M)
    (k : ℤ) (t : ℝ) (he : M * (ω + k) - (x : ℕ) = t) (ht : |t| ≤ 1) :
    circDist ((x : ℕ) / (M : ℝ)) ω ≤ 1 / (M : ℝ) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have he' : (k : ℝ) + ω - (x : ℕ) / M = t / M := by
    apply (eq_div_iff (ne_of_gt hm)).2
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hm)]
    nlinarith [he]
  calc
    _ ≤ |(k : ℝ) + ω - (x : ℕ) / M| :=
      ciInf_le (show BddBelow (Set.range fun z : ℤ => |(z : ℝ) + ω - (x : ℕ) / M|) from
        ⟨0, by rintro _ ⟨z, rfl⟩; exact abs_nonneg _⟩) k
    _ = |t| / M := by rw [he', abs_div, abs_of_pos hm]
    _ ≤ 1 / M := div_le_div_of_nonneg_right ht hm.le

private lemma fc_exact (M : ℕ) (hM : M ≠ 0) (ω : ℝ) (x : Fin M)
    (he : M * ω = (x : ℕ)) : phaseProb M ω x = 1 := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have hd : ω - (x : ℕ) / M = 0 := by apply sub_eq_zero.mpr; exact (eq_div_iff hm).2 (by nlinarith)
  rw [phaseProb, fc_amplitude M hM ω x, hd]
  simp [hM]

private lemma fc_pair_bound (t p q : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hp : Real.sin (π * t) ^ 2 ≤ p * (π * t) ^ 2)
    (hq : Real.sin (π * (t - 1)) ^ 2 ≤ q * (π * (t - 1)) ^ 2) :
    8 / π ^ 2 ≤ p + q := by
  have hs : Real.sin (π * (t - 1)) ^ 2 = Real.sin (π * t) ^ 2 := by
    rw [show π * (t - 1) = -(π - π * t) by ring, Real.sin_neg, Real.sin_pi_sub]
    ring
  rw [hs] at hq
  have h1 := mul_le_mul_of_nonneg_right hp (sq_nonneg (1 - t))
  have h2 := mul_le_mul_of_nonneg_right hq (sq_nonneg t)
  have h3 := fc_sine_pair t ht0.le ht1.le
  have hh : 8 * (t ^ 2 * (1 - t) ^ 2) ≤
      ((p + q) * π ^ 2) * (t ^ 2 * (1 - t) ^ 2) := by
    nlinarith only [h1, h2, h3]
  have hc : 8 ≤ (p + q) * π ^ 2 :=
    (mul_le_mul_iff_left₀ (show 0 < t ^ 2 * (1 - t) ^ 2 by positivity)).1 (by simpa [mul_comm] using hh)
  exact (div_le_iff₀ (by positivity : 0 < π ^ 2)).2 hc

theorem solution (M : ℕ) (hM2 : 2 < M) (ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω < 1) :
    8 / π ^ 2 ≤
      ∑ x ∈ Finset.univ.filter
          (fun x : Fin M => circDist (((x : ℕ) : ℝ) / (M : ℝ)) ω ≤ 1 / (M : ℝ)),
        phaseProb M ω x := by
  classical
  have hMpos : 0 < M := by omega
  have hM : M ≠ 0 := by omega
  have hm : (0 : ℝ) < M := by exact_mod_cast hMpos
  let a : ℕ := ⌊(M : ℝ) * ω⌋₊
  have hmw0 : 0 ≤ (M : ℝ) * ω := mul_nonneg hm.le hω0
  have ha : a < M := (Nat.floor_lt hmw0).2 (by nlinarith)
  let x : Fin M := ⟨a, ha⟩
  let t : ℝ := M * ω - a
  have ht0 : 0 ≤ t := sub_nonneg.mpr (Nat.floor_le hmw0)
  have ht1 : t < 1 := by dsimp [t, a]; linarith [Nat.lt_floor_add_one ((M : ℝ) * ω)]
  let E := Finset.univ.filter
    (fun x : Fin M => circDist (((x : ℕ) : ℝ) / (M : ℝ)) ω ≤ 1 / (M : ℝ))
  have hx : x ∈ E := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, fc_dist_bound M hMpos ω x 0 t ?_ ?_⟩
    · simp only [Int.cast_zero, add_zero]; rfl
    · exact abs_le.mpr ⟨by linarith, ht1.le⟩
  have hnonneg (z : Fin M) : 0 ≤ phaseProb M ω z := Complex.normSq_nonneg _
  change 8 / π ^ 2 ≤ ∑ z ∈ E, phaseProb M ω z
  by_cases ht : t = 0
  · have hp : phaseProb M ω x = 1 := by
      apply fc_exact M hM ω x
      change (M : ℝ) * ω = a
      exact sub_eq_zero.mp ht
    calc
      8 / π ^ 2 ≤ 1 := (div_le_one (by positivity : 0 < π ^ 2)).2 (by nlinarith [Real.pi_gt_three])
      _ = phaseProb M ω x := hp.symm
      _ ≤ ∑ z ∈ E, phaseProb M ω z := Finset.single_le_sum (fun z _ => hnonneg z) hx
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    obtain ⟨y, k, hxy, he⟩ : ∃ y : Fin M, ∃ k : ℤ,
        x ≠ y ∧ M * (ω + k) - (y : ℕ) = t - 1 := by
      by_cases hb : a + 1 < M
      · refine ⟨⟨a + 1, hb⟩, 0, ?_, ?_⟩
        · intro h
          have hv := congrArg Fin.val h
          dsimp [x] at hv
          omega
        · dsimp [t]
          push_cast
          ring
      · have hb' : a + 1 = M := by omega
        refine ⟨⟨0, hMpos⟩, -1, ?_, ?_⟩
        · intro h
          have hv := congrArg Fin.val h
          dsimp [x] at hv
          omega
        · have hcast : (a : ℝ) + 1 = M := by exact_mod_cast hb'
          dsimp [t]
          push_cast
          nlinarith
    have hy : y ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fc_dist_bound M hMpos ω y k (t - 1) he (abs_le.mpr ⟨by linarith, by linarith⟩)⟩
    have hp : Real.sin (π * t) ^ 2 ≤ phaseProb M ω x * (π * t) ^ 2 := by
      exact fc_prob_lower M hM ω x
    have hq : Real.sin (π * (t - 1)) ^ 2 ≤ phaseProb M ω y * (π * (t - 1)) ^ 2 := by
      have h := fc_prob_lower M hM (ω + k) y
      rw [he, fc_prob_periodic] at h
      exact h
    calc
      8 / π ^ 2 ≤ phaseProb M ω x + phaseProb M ω y := fc_pair_bound t _ _ htpos ht1 hp hq
      _ = ∑ z ∈ ({x, y} : Finset (Fin M)), phaseProb M ω z := by simp [hxy]
      _ ≤ ∑ z ∈ E, phaseProb M ω z := Finset.sum_le_sum_of_subset_of_nonneg
        (by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption)
        (fun z _ _ => hnonneg z)
