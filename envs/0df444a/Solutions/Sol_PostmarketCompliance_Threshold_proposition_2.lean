-- Prove2me | solution 1 for PostmarketCompliance.Threshold.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T17:26:18.204307+00:00
-- url     : https://prove2.me/submissions/8c30faf4-640e-4fd1-bb5c-01687aea6caa

import Mathlib
import Definitions.Def_PostmarketCompliance_Threshold_Model

set_option autoImplicit false

namespace PMC1023

open Real intervalIntegral MeasureTheory Set

/-- average of `f` over `min (d + Exp(r)) T` -/
noncomputable def Sop (T r : ℝ) (f : ℝ → ℝ) (d : ℝ) : ℝ :=
  r * exp (r * d) * (∫ x in d..T, exp (-(r * x)) * f x) + exp (-(r * (T - d))) * f T

lemma Sop_T (T r : ℝ) (f : ℝ → ℝ) : Sop T r f T = f T := by
  simp [Sop]

lemma hasDerivAt_Sop (T r : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (d : ℝ) :
    HasDerivAt (Sop T r f) (r * (Sop T r f d - f d)) d := by
  have hc : Continuous (fun x => exp (-(r * x)) * f x) := by fun_prop
  have h1 : HasDerivAt (fun d => ∫ x in d..T, exp (-(r * x)) * f x)
      (-(exp (-(r * d)) * f d)) d := by
    have := (hc.integral_hasStrictDerivAt T d).hasDerivAt.neg
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [integral_symm]
    rfl
  have h2 : HasDerivAt (fun d => exp (r * d)) (exp (r * d) * r) d := by
    have := ((hasDerivAt_id d).const_mul r).exp
    simpa using this
  have h3 : HasDerivAt (fun d => exp (-(r * (T - d)))) (exp (-(r * (T - d))) * r) d := by
    have := (((hasDerivAt_id d).const_sub T).const_mul r).neg.exp
    simpa using this
  have h := ((h2.const_mul r).mul h1).add (h3.mul_const (f T))
  have e : exp (r * d) * exp (-(r * d)) = 1 := by rw [← exp_add]; simp
  have hd : r * (exp (r * d) * r) * (∫ x in d..T, exp (-(r * x)) * f x)
      + r * exp (r * d) * (-(exp (-(r * d)) * f d)) + exp (-(r * (T - d))) * r * f T
      = r * (Sop T r f d - f d) := by
    simp only [Sop]
    linear_combination (-(r * f d)) * e
  exact h.congr_deriv hd

lemma continuous_Sop (T r : ℝ) {f : ℝ → ℝ} (hf : Continuous f) : Continuous (Sop T r f) :=
  continuous_iff_continuousAt.2 fun d => (hasDerivAt_Sop T r hf d).continuousAt

lemma Sop_mixture {T s s' : ℝ} (hs' : 0 < s') {G : ℝ → ℝ} (hG : Continuous G) (d : ℝ) :
    Sop T s G d = (s / s') * Sop T s' G d + (1 - s / s') * Sop T s (Sop T s' G) d := by
  have hvc : Continuous (Sop T s' G) := continuous_Sop T s' hG
  have hu' : ∀ x, HasDerivAt (Sop T s G) (s * (Sop T s G x - G x)) x :=
    fun x => hasDerivAt_Sop T s hG x
  have hw' : ∀ x, HasDerivAt
      (fun x => (s / s') * Sop T s' G x + (1 - s / s') * Sop T s (Sop T s' G) x)
      (s * ((s / s') * Sop T s' G x + (1 - s / s') * Sop T s (Sop T s' G) x - G x)) x := by
    intro x
    have := ((hasDerivAt_Sop T s' hG x).const_mul (s / s')).add
      ((hasDerivAt_Sop T s hvc x).const_mul (1 - s / s'))
    refine this.congr_deriv ?_
    field_simp
    ring
  have hz : ∀ x, HasDerivAt (fun x => exp (-(s * x)) * (Sop T s G x -
      ((s / s') * Sop T s' G x + (1 - s / s') * Sop T s (Sop T s' G) x))) 0 x := by
    intro x
    have he : HasDerivAt (fun x => exp (-(s * x))) (exp (-(s * x)) * (-s)) x := by
      have := ((hasDerivAt_id x).const_mul s).neg.exp
      simpa using this
    have := he.mul ((hu' x).sub (hw' x))
    exact this.congr_deriv (by simp only [Pi.sub_apply]; ring)
  have hconst := is_const_of_deriv_eq_zero (fun x => (hz x).differentiableAt)
    (fun x => (hz x).deriv) d T
  simp only [Sop_T] at hconst
  have hne : exp (-(s * d)) ≠ 0 := (exp_pos _).ne'
  have h0 : G T - (s / s' * G T + (1 - s / s') * G T) = 0 := by ring
  rw [h0, mul_zero] at hconst
  rcases mul_eq_zero.1 hconst with h | h
  · exact absurd h hne
  · linarith

lemma integral_exp_neg_mul {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    ∫ x in a..b, exp (-(r * x)) = (exp (-(r * a)) - exp (-(r * b))) / r := by
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x => -exp (-(r * x)) / r) (exp (-(r * x))) x := by
    intro x _
    have := (((hasDerivAt_id x).const_mul r).neg.exp.neg).div_const r
    refine this.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
    rfl
  rw [integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun x => exp (-(r * x))).intervalIntegrable _ _)]
  ring

/-- averaging bound: with an exact deficit from the atom at `T` -/
lemma Sop_le {T r M : ℝ} (hr : 0 < r) {d : ℝ} (hd : d ≤ T) {v : ℝ → ℝ} (hv : Continuous v)
    (hM : ∀ x ∈ Icc d T, v x ≤ M) :
    Sop T r v d ≤ M - exp (-(r * (T - d))) * (M - v T) := by
  have hint : ∫ x in d..T, exp (-(r * x)) * v x ≤ ∫ x in d..T, exp (-(r * x)) * M := by
    apply intervalIntegral.integral_mono_on hd
    · exact (by fun_prop : Continuous fun x => exp (-(r * x)) * v x).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun x => exp (-(r * x)) * M).intervalIntegrable _ _
    · intro x hx
      exact mul_le_mul_of_nonneg_left (hM x hx) (exp_pos _).le
  rw [intervalIntegral.integral_mul_const, integral_exp_neg_mul hr] at hint
  have e1 : exp (r * d) * exp (-(r * d)) = 1 := by rw [← exp_add]; simp
  have e2 : exp (r * d) * exp (-(r * T)) = exp (-(r * (T - d))) := by rw [← exp_add]; ring_nf
  have hpos : 0 < r * exp (r * d) := mul_pos hr (exp_pos _)
  have := mul_le_mul_of_nonneg_left hint hpos.le
  simp only [Sop]
  have key : r * exp (r * d) * ((exp (-(r * d)) - exp (-(r * T))) / r * M)
      = M - exp (-(r * (T - d))) * M := by
    have hr0 : r ≠ 0 := hr.ne'
    calc r * exp (r * d) * ((exp (-(r * d)) - exp (-(r * T))) / r * M)
        = (exp (r * d) * exp (-(r * d)) - exp (r * d) * exp (-(r * T))) * M := by
          field_simp
      _ = M - exp (-(r * (T - d))) * M := by rw [e1, e2]; ring
  nlinarith

/-- the mixture bound: `u = Sop s G` is at most the max `M` of `v = Sop s' G`, with a deficit
from the atom at `T` when `s < s'` -/
lemma mixture_le {T s s' M : ℝ} (hs : 0 < s) (hss : s ≤ s') {G : ℝ → ℝ} (hG : Continuous G)
    {d : ℝ} (hd : d ≤ T) (hM : ∀ x ∈ Icc d T, Sop T s' G x ≤ M) :
    Sop T s G d ≤ M - (1 - s / s') * exp (-(s * (T - d))) * (M - G T) := by
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  rw [Sop_mixture hs' hG d]
  have h1 := Sop_le hs hd (continuous_Sop T s' hG) hM
  rw [Sop_T] at h1
  have h2 : Sop T s' G d ≤ M := hM d ⟨le_rfl, hd⟩
  have hq : 0 ≤ s / s' := div_nonneg hs.le hs'.le
  have hq1 : 0 ≤ 1 - s / s' := by rw [sub_nonneg, div_le_one hs']; exact hss
  nlinarith [mul_le_mul_of_nonneg_left h1 hq1, mul_le_mul_of_nonneg_left h2 hq]

/-- near `T`: if `G` exceeds `G T` on `(y, T)` then so does its average -/
lemma Sop_gt_T {T r : ℝ} (hr : 0 < r) {G : ℝ → ℝ} (hG : Continuous G) {y : ℝ} (hy : y < T)
    (hpos : ∀ x ∈ Ioo y T, G T < G x) : G T < Sop T r G y := by
  have hc1 : Continuous fun x => exp (-(r * x)) * G x := by fun_prop
  have hc2 : Continuous fun x => exp (-(r * x)) * G T := by fun_prop
  have hI : 0 < ∫ x in y..T, (exp (-(r * x)) * G x - exp (-(r * x)) * G T) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (hc1.sub hc2).intervalIntegrable _ _
    · intro x hx
      have := hpos x hx
      have := exp_pos (-(r * x))
      nlinarith
    · exact hy
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, integral_exp_neg_mul hr] at hI
  have e1 : exp (r * y) * exp (-(r * y)) = 1 := by rw [← exp_add]; simp
  have e2 : exp (r * y) * exp (-(r * T)) = exp (-(r * (T - y))) := by rw [← exp_add]; ring_nf
  have hpos' : 0 < r * exp (r * y) := mul_pos hr (exp_pos _)
  have := mul_pos hpos' hI
  simp only [Sop]
  have key : r * exp (r * y) * ((exp (-(r * y)) - exp (-(r * T))) / r * G T)
      = G T - exp (-(r * (T - y))) * G T := by
    have hr0 : r ≠ 0 := hr.ne'
    calc r * exp (r * y) * ((exp (-(r * y)) - exp (-(r * T))) / r * G T)
        = (exp (r * y) * exp (-(r * y)) - exp (r * y) * exp (-(r * T))) * G T := by
          field_simp
      _ = G T - exp (-(r * (T - y))) * G T := by rw [e1, e2]; ring
  nlinarith

/-! ## Part C: the deterministic-deadline gain `Gm` -/

open PostmarketCompliance.Threshold

/-- gamma density with natural powers -/
noncomputable def pdf' (n : ℕ) (lam t : ℝ) : ℝ :=
  lam ^ n * t ^ (n - 1) * exp (-(lam * t)) / ((n - 1).factorial : ℝ)

lemma continuous_pdf'_t (n : ℕ) (lam : ℝ) : Continuous (pdf' n lam) := by
  unfold pdf'; fun_prop

lemma pdf'_nonneg (n : ℕ) {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t) : 0 ≤ pdf' n lam t := by
  unfold pdf'; positivity

lemma pdf'_pos (n : ℕ) {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) : 0 < pdf' n lam t := by
  unfold pdf'; positivity

lemma pdf'_le (n : ℕ) {lam t T : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t) (htT : t ≤ T) :
    pdf' n lam t ≤ lam ^ n * T ^ (n - 1) / ((n - 1).factorial : ℝ) := by
  unfold pdf'
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 : exp (-(lam * t)) ≤ 1 := by
    rw [exp_le_one_iff]; nlinarith
  have h2 : t ^ (n - 1) ≤ T ^ (n - 1) := pow_le_pow_left₀ ht htT _
  have h3 : 0 ≤ lam ^ n := by positivity
  calc lam ^ n * t ^ (n - 1) * exp (-(lam * t)) ≤ lam ^ n * t ^ (n - 1) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ lam ^ n * T ^ (n - 1) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left h2 h3

/-- deterministic-deadline gain: withdrawal exactly at `min x T` -/
noncomputable def Gm (P : Params) (lam x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..min x P.T,
    ((P.T - t) * P.alpha * P.piR - P.piA * (min x P.T - t)) * pdf' P.n lam t

lemma Gm_eq (P : Params) (lam x : ℝ) : Gm P lam x =
    (∫ t in (0 : ℝ)..min x P.T, ((P.T - t) * P.alpha * P.piR + P.piA * t) * pdf' P.n lam t)
      - P.piA * min x P.T * ∫ t in (0 : ℝ)..min x P.T, pdf' P.n lam t := by
  have hc := continuous_pdf'_t P.n lam
  unfold Gm
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun t =>
      ((P.T - t) * P.alpha * P.piR + P.piA * t) * pdf' P.n lam t).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => P.piA * min x P.T * pdf' P.n lam t).intervalIntegrable _ _)]
  congr 1; ext t; ring

lemma continuous_Gm (P : Params) : Continuous (fun p : ℝ × ℝ => Gm P p.1 p.2) := by
  have h1 := intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume)
    (a₀ := 0) (f := fun lam t => ((P.T - t) * P.alpha * P.piR + P.piA * t) * pdf' P.n lam t)
    (by rw [Function.uncurry_def]; simp only [pdf']; fun_prop)
  have h2 := intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume)
    (a₀ := 0) (f := fun lam t => pdf' P.n lam t)
    (by rw [Function.uncurry_def]; simp only [pdf']; fun_prop)
  have hm : Continuous fun p : ℝ × ℝ => (p.1, min p.2 P.T) := by fun_prop
  have h3 : Continuous fun p : ℝ × ℝ => P.piA * min p.2 P.T := by fun_prop
  have := (h1.comp hm).sub (h3.mul (h2.comp hm))
  refine this.congr fun p => ?_
  simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply, Gm_eq]

lemma continuous_Gm_x (P : Params) (lam : ℝ) : Continuous (Gm P lam) :=
  (continuous_Gm P).comp (continuous_const.prodMk continuous_id)

lemma int_mono_upper {f : ℝ → ℝ} (hf : Continuous f) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hpos : ∀ t ∈ Icc a c, 0 ≤ f t) : ∫ t in a..b, f t ≤ ∫ t in a..c, f t :=
  intervalIntegral.integral_mono_interval le_rfl hab hbc
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht =>
      hpos t ⟨ht.1.le, ht.2⟩)) (hf.intervalIntegrable _ _)

lemma Gm_le {P : Params} (hP : P.Standing) {lam x : ℝ} (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    Gm P lam x ≤ P.T * P.piR * ∫ t in (0 : ℝ)..P.T, pdf' P.n lam t := by
  obtain ⟨hT, hA, hAR, ha, ha1, hs, hk, hkn⟩ := hP
  have hc := continuous_pdf'_t P.n lam
  have hm0 : 0 ≤ min x P.T := le_min hx hT.le
  have hmT : min x P.T ≤ P.T := min_le_right _ _
  have step1 : Gm P lam x ≤ ∫ t in (0 : ℝ)..min x P.T, P.T * P.piR * pdf' P.n lam t := by
    unfold Gm
    apply intervalIntegral.integral_mono_on hm0
    · exact (by fun_prop : Continuous fun t =>
        ((P.T - t) * P.alpha * P.piR - P.piA * (min x P.T - t)) * pdf' P.n lam t).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun t => P.T * P.piR * pdf' P.n lam t).intervalIntegrable _ _
    · intro t ht
      have hp := pdf'_nonneg P.n hlam ht.1
      apply mul_le_mul_of_nonneg_right _ hp
      have : (P.T - t) * P.alpha * P.piR ≤ P.T * P.piR := by
        have h1 : (P.T - t) * P.alpha ≤ P.T := by nlinarith [ht.1, ht.2]
        nlinarith
      nlinarith [ht.2]
  have step2 := int_mono_upper (f := fun t => P.T * P.piR * pdf' P.n lam t)
    (by fun_prop) hm0 hmT (fun t ht => mul_nonneg (mul_nonneg hT.le (by linarith))
      (pdf'_nonneg P.n hlam ht.1))
  simp only [intervalIntegral.integral_const_mul] at step1 step2
  linarith

lemma int_pdf'_le_pow {n : ℕ} (hn : 1 ≤ n) {lam T : ℝ} (hlam : 0 ≤ lam) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, pdf' n lam t ≤ lam ^ n * T ^ n / (n.factorial : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hc := continuous_pdf'_t (m + 1) lam
  have h1 : ∫ t in (0 : ℝ)..T, pdf' (m + 1) lam t
      ≤ ∫ t in (0 : ℝ)..T, lam ^ (m + 1) / (m.factorial : ℝ) * t ^ m := by
    apply intervalIntegral.integral_mono_on hT (hc.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t : ℝ => lam ^ (m + 1) / (m.factorial : ℝ) * t ^ m).intervalIntegrable _ _)
    intro t ht
    unfold pdf'
    simp only [Nat.add_sub_cancel]
    have h1 : exp (-(lam * t)) ≤ 1 := by
      rw [exp_le_one_iff]; nlinarith [ht.1]
    have h2 : 0 ≤ lam ^ (m + 1) * t ^ m := by have := ht.1; positivity
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc lam ^ (m + 1) * t ^ m * exp (-(lam * t)) ≤ lam ^ (m + 1) * t ^ m * 1 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = lam ^ (m + 1) * t ^ m := by ring
  rw [intervalIntegral.integral_const_mul, integral_pow] at h1
  refine h1.trans (le_of_eq ?_)
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma Gm_near_T {P : Params} (hP : P.Standing) {lam : ℝ} (hlam : 0 < lam) :
    ∃ δ > 0, ∀ x ∈ Ioo (P.T - δ) P.T, Gm P lam P.T < Gm P lam x := by
  obtain ⟨hT, hA, hAR, ha, ha1, hs, hk, hkn⟩ := hP
  have hc := continuous_pdf'_t P.n lam
  set B := lam ^ P.n * P.T ^ (P.n - 1) / ((P.n - 1).factorial : ℝ) with hBdef
  have hB : 0 < B := by positivity
  set P0 := ∫ t in (0 : ℝ)..P.T / 2, pdf' P.n lam t with hP0def
  have hP0 : 0 < P0 := intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
    (fun t ht => pdf'_pos _ hlam ht.1) (by linarith)
  have hR : 0 < P.piR := by linarith
  refine ⟨min (P.T / 2) (P.piA * P0 / (P.piR * B)), by positivity, ?_⟩
  intro x hx
  have hx1 : P.T - x < P.T / 2 := by
    have := min_le_left (P.T / 2) (P.piA * P0 / (P.piR * B)); linarith [hx.1]
  have hx2 : P.T - x < P.piA * P0 / (P.piR * B) := by
    have := min_le_right (P.T / 2) (P.piA * P0 / (P.piR * B)); linarith [hx.1]
  have hxT := hx.2
  have hx0 : 0 ≤ x := by linarith
  have hmx : min x P.T = x := min_eq_left hxT.le
  have hfc : Continuous fun t => ((P.T - t) * P.alpha * P.piR - P.piA * (P.T - t)) * pdf' P.n lam t := by
    fun_prop
  have hGT : Gm P lam P.T =
      (∫ t in (0 : ℝ)..x, ((P.T - t) * P.alpha * P.piR - P.piA * (P.T - t)) * pdf' P.n lam t)
      + ∫ t in x..P.T, ((P.T - t) * P.alpha * P.piR - P.piA * (P.T - t)) * pdf' P.n lam t := by
    unfold Gm
    rw [min_self, intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _)]
  have hGx : Gm P lam x =
      (∫ t in (0 : ℝ)..x, ((P.T - t) * P.alpha * P.piR - P.piA * (P.T - t)) * pdf' P.n lam t)
      + P.piA * (P.T - x) * ∫ t in (0 : ℝ)..x, pdf' P.n lam t := by
    unfold Gm
    rw [hmx, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (hfc.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => P.piA * (P.T - x) * pdf' P.n lam t).intervalIntegrable _ _)]
    congr 1; ext t; ring
  have hup : ∫ t in x..P.T, ((P.T - t) * P.alpha * P.piR - P.piA * (P.T - t)) * pdf' P.n lam t
      ≤ ∫ t in x..P.T, (P.T - x) * P.piR * B := by
    apply intervalIntegral.integral_mono_on hxT.le (hfc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
    intro t ht
    have hp0 := pdf'_nonneg P.n hlam.le (hx0.trans ht.1)
    have hpB : pdf' P.n lam t ≤ B := pdf'_le P.n hlam.le (hx0.trans ht.1) ht.2
    have e1 : (P.T - t) * P.alpha * P.piR ≤ (P.T - x) * P.piR := by
      have : (P.T - t) * P.alpha ≤ P.T - x := by nlinarith [ht.1, ht.2]
      nlinarith
    have e2 : 0 ≤ (P.T - t) * P.alpha * P.piR := by
      have : 0 ≤ P.T - t := by linarith [ht.2]
      positivity
    have e3 : 0 ≤ P.piA * (P.T - t) := by nlinarith [ht.2]
    calc ((P.T - t) * P.alpha * P.piR - P.piA * (P.T - t)) * pdf' P.n lam t
        ≤ (P.T - t) * P.alpha * P.piR * pdf' P.n lam t := by nlinarith
      _ ≤ (P.T - x) * P.piR * pdf' P.n lam t := mul_le_mul_of_nonneg_right e1 hp0
      _ ≤ (P.T - x) * P.piR * B := by
          apply mul_le_mul_of_nonneg_left hpB; nlinarith
  rw [intervalIntegral.integral_const] at hup
  simp only [smul_eq_mul] at hup
  have hlow : P0 ≤ ∫ t in (0 : ℝ)..x, pdf' P.n lam t :=
    int_mono_upper hc (by linarith) (by linarith) (fun t ht => pdf'_nonneg P.n hlam.le ht.1)
  have hx2' : (P.T - x) * (P.piR * B) < P.piA * P0 := by
    rwa [lt_div_iff₀ (by positivity)] at hx2
  have hpos : 0 < P.T - x := by linarith
  rw [hGT, hGx]
  nlinarith [mul_le_mul_of_nonneg_left hlow (by positivity : (0:ℝ) ≤ P.piA * (P.T - x)),
    mul_lt_mul_of_pos_left hx2' hpos]

lemma Gm_alpha {P : Params} (ha : 0 < P.alpha) (hA : 0 < P.piA) {α₂ : ℝ} (hα : P.alpha ≤ α₂)
    {lam x : ℝ} (hlam : 0 ≤ lam) (hx : 0 ≤ x) (hT : 0 < P.T) :
    (α₂ / P.alpha) * Gm P lam x ≤ Gm { P with alpha := α₂ } lam x := by
  have hc := continuous_pdf'_t P.n lam
  have hm0 : 0 ≤ min x P.T := le_min hx hT.le
  unfold Gm
  simp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hm0
  · exact (by fun_prop : Continuous fun t => α₂ / P.alpha *
      (((P.T - t) * P.alpha * P.piR - P.piA * (min x P.T - t)) * pdf' P.n lam t)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun t =>
      ((P.T - t) * α₂ * P.piR - P.piA * (min x P.T - t)) * pdf' P.n lam t).intervalIntegrable _ _
  · intro t ht
    have hp := pdf'_nonneg P.n hlam ht.1
    have q : 1 ≤ α₂ / P.alpha := (one_le_div ha).2 hα
    have key : ((P.T - t) * α₂ * P.piR - P.piA * (min x P.T - t)) * pdf' P.n lam t
        - α₂ / P.alpha * (((P.T - t) * P.alpha * P.piR - P.piA * (min x P.T - t)) * pdf' P.n lam t)
        = (α₂ / P.alpha - 1) * (P.piA * ((min x P.T - t) * pdf' P.n lam t)) := by
      field_simp
      ring
    have : 0 ≤ (α₂ / P.alpha - 1) * (P.piA * ((min x P.T - t) * pdf' P.n lam t)) := by
      have : 0 ≤ min x P.T - t := by linarith [ht.2]
      apply mul_nonneg (by linarith)
      positivity
    linarith

/-! ## Part R: representation of the gain -/

open ProbabilityTheory

lemma gammaPDFReal_eq_pdf' {n : ℕ} (hn : 1 ≤ n) (lam : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    gammaPDFReal (n : ℝ) lam t = pdf' n lam t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold gammaPDFReal pdf'
  rw [if_pos ht]
  have h1 : ((m + 1 : ℕ) : ℝ) - 1 = ((m : ℕ) : ℝ) := by push_cast; ring
  have h2 : Real.Gamma ((m + 1 : ℕ) : ℝ) = (m.factorial : ℝ) := by
    rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by push_cast; ring]
    exact Real.Gamma_nat_eq_factorial m
  rw [h1, h2, Real.rpow_natCast, Real.rpow_natCast, Nat.add_sub_cancel]
  ring

lemma integral_gamma {n : ℕ} (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 < lam) (f : ℝ → ℝ) :
    ∫ t, f t ∂(gammaMeasure (n : ℝ) lam) = ∫ t in Ici 0, pdf' n lam t * f t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (by exact (measurable_gammaPDFReal _ _).ennreal_ofReal : Measurable (gammaPDF (n : ℝ) lam))
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hz : ∀ t, t ∉ Ici (0 : ℝ) → (gammaPDF (n : ℝ) lam t).toReal • f t = 0 := by
    intro t ht
    simp only [mem_Ici, not_le] at ht
    simp [gammaPDF_of_neg ht]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
  simp only [gammaPDF, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg hn' hlam t), gammaPDFReal_eq_pdf' hn lam ht]

lemma integral_pdf'_Ici {n : ℕ} (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 < lam) :
    ∫ t in Ici 0, pdf' n lam t = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  haveI := isProbabilityMeasure_gammaMeasure hn' hlam
  have := integral_gamma hn hlam (fun _ => 1)
  simpa using this.symm

lemma integrableOn_pdf' {n : ℕ} (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn (pdf' n lam) (Ici 0) :=
  Integrable.of_integral_ne_zero (by rw [integral_pdf'_Ici hn hlam]; norm_num)

lemma int_pdf'_le_one {n : ℕ} (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 < lam) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, pdf' n lam t ≤ 1 := by
  rw [intervalIntegral.integral_of_le hT, ← integral_pdf'_Ici hn hlam]
  exact setIntegral_mono_set (integrableOn_pdf' hn hlam)
    ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun t ht => pdf'_nonneg n hlam.le ht))
    (LE.le.eventuallyLE (fun x hx => le_of_lt hx.1 : Ioc (0:ℝ) T ⊆ Ici 0))

lemma ae_nonneg_gamma (a r : ℝ) : ∀ᵐ x ∂(gammaMeasure a r), 0 ≤ x := by
  rw [ae_iff]
  have : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by ext; simp
  rw [this]
  unfold gammaMeasure
  rw [withDensity_apply _ measurableSet_Iio,
    setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
      (fun x hx => gammaPDF_of_neg hx)]
  simp

lemma Fphi_eq (P : Params) (d t τ : ℝ) : phi P d t τ - dTilde P d τ * P.piA =
    if t ≤ min (d + τ) P.T then
      (P.T - t) * P.alpha * P.piR - P.piA * (min (d + τ) P.T - t) else 0 := by
  unfold phi dTilde
  split_ifs <;> ring

lemma measurable_phi (P : Params) (d : ℝ) : Measurable (fun p : ℝ × ℝ => phi P d p.1 p.2) := by
  unfold phi dTilde
  refine Measurable.ite ?_ (Continuous.measurable (by fun_prop))
    (Continuous.measurable (by fun_prop))
  exact measurableSet_le measurable_fst (Continuous.measurable (by fun_prop))

lemma Gm_of_ge {P : Params} {lam x : ℝ} (hx : P.T ≤ x) : Gm P lam x = Gm P lam P.T := by
  unfold Gm; rw [min_eq_right hx, min_self]

set_option maxHeartbeats 1000000 in
lemma gain_eq {P : Params} (hP : P.Standing) {d lam : ℝ} (hd0 : 0 ≤ d) (hdT : d ≤ P.T)
    (hlam : 0 < lam) :
    (∫ t, expectedPhi P d t ∂(gammaMeasure (P.n : ℝ) lam)) - profitN P d
      = Sop P.T P.s (Gm P lam) d := by
  obtain ⟨hT, hA, hAR, ha, ha1, hs, hk, hkn⟩ := hP
  have hn1 : 1 ≤ P.n := by
    have : (1 : ℝ) < P.n := lt_of_le_of_lt hk hkn
    exact_mod_cast this.le
  have hn' : (0 : ℝ) < P.n := by exact_mod_cast hn1
  have hΓ : IsProbabilityMeasure (gammaMeasure (P.n : ℝ) lam) :=
    isProbabilityMeasure_gammaMeasure hn' hlam
  have hE : IsProbabilityMeasure (expMeasure P.s) := isProbabilityMeasure_expMeasure hs
  have aeE : ∀ᵐ τ ∂(expMeasure P.s), 0 ≤ τ := ae_nonneg_gamma 1 P.s
  have aeΓ : ∀ᵐ t ∂(gammaMeasure (P.n : ℝ) lam), 0 ≤ t := ae_nonneg_gamma _ _
  set CF := P.T * (P.piR + P.piA) with hCF
  have hF : ∀ t τ, 0 ≤ t → 0 ≤ τ → |phi P d t τ - dTilde P d τ * P.piA| ≤ CF := by
    intro t τ ht hτ
    rw [Fphi_eq]
    split_ifs with h
    · have hm : min (d + τ) P.T ≤ P.T := min_le_right _ _
      have h1 : 0 ≤ (P.T - t) * P.alpha * P.piR := by
        have : 0 ≤ P.T - t := by linarith
        have : 0 ≤ P.piR := by linarith
        positivity
      have h2 : (P.T - t) * P.alpha * P.piR ≤ P.T * P.piR := by
        have : (P.T - t) * P.alpha ≤ P.T := by nlinarith
        nlinarith
      have h3 : 0 ≤ P.piA * (min (d + τ) P.T - t) := by nlinarith
      have h4 : P.piA * (min (d + τ) P.T - t) ≤ P.T * P.piA := by nlinarith
      rw [abs_le]; constructor <;> nlinarith
    · simp only [abs_zero]; exact mul_nonneg hT.le (by linarith)
  have hD : ∀ τ, 0 ≤ τ → |dTilde P d τ * P.piA| ≤ P.T * P.piA := by
    intro τ hτ
    unfold dTilde
    have h0 : 0 ≤ min (d + τ) P.T := le_min (by linarith) hT.le
    rw [abs_of_nonneg (mul_nonneg h0 hA.le)]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) hA.le
  have hmphi := measurable_phi P d
  have hmD : Measurable (fun τ => dTilde P d τ * P.piA) := by
    unfold dTilde; exact Continuous.measurable (by fun_prop)
  have hmF : Measurable (fun p : ℝ × ℝ => phi P d p.1 p.2 - dTilde P d p.2 * P.piA) :=
    hmphi.sub (hmD.comp measurable_snd)
  -- claim 1
  have claim1 : ∀ t, 0 ≤ t → expectedPhi P d t =
      (∫ τ, (phi P d t τ - dTilde P d τ * P.piA) ∂(expMeasure P.s)) + profitN P d := by
    intro t ht
    have hI1 : Integrable (fun τ => phi P d t τ - dTilde P d τ * P.piA) (expMeasure P.s) :=
      Integrable.of_bound (hmF.comp measurable_prodMk_left).aestronglyMeasurable CF
        (aeE.mono fun τ hτ => by rw [Real.norm_eq_abs]; exact hF t τ ht hτ)
    have hI2 : Integrable (fun τ => dTilde P d τ * P.piA) (expMeasure P.s) :=
      Integrable.of_bound hmD.aestronglyMeasurable (P.T * P.piA)
        (aeE.mono fun τ hτ => by rw [Real.norm_eq_abs]; exact hD τ hτ)
    unfold expectedPhi profitN
    rw [← integral_add hI1 hI2]
    congr 1; ext τ; ring
  set Ψ := fun t => ∫ τ, (phi P d t τ - dTilde P d τ * P.piA) ∂(expMeasure P.s) with hΨ
  have hΨm : StronglyMeasurable Ψ :=
    StronglyMeasurable.integral_prod_right
      (f := fun t τ => phi P d t τ - dTilde P d τ * P.piA) hmF.stronglyMeasurable
  have hΨint : Integrable Ψ (gammaMeasure (P.n : ℝ) lam) := by
    refine Integrable.of_bound hΨm.aestronglyMeasurable CF (aeΓ.mono fun t ht => ?_)
    have := norm_integral_le_of_norm_le_const (μ := expMeasure P.s)
      (f := fun τ => phi P d t τ - dTilde P d τ * P.piA) (C := CF)
      (aeE.mono fun τ hτ => by rw [Real.norm_eq_abs]; exact hF t τ ht hτ)
    simpa using this
  have claim2 : ∫ t, expectedPhi P d t ∂(gammaMeasure (P.n : ℝ) lam)
      = (∫ t, Ψ t ∂(gammaMeasure (P.n : ℝ) lam)) + profitN P d := by
    rw [integral_congr_ae (aeΓ.mono fun t ht => claim1 t ht),
      integral_add hΨint (integrable_const _)]
    simp
  -- claim 3: Fubini
  have aeprod : ∀ᵐ p ∂((gammaMeasure (P.n : ℝ) lam).prod (expMeasure P.s)), 0 ≤ p.1 ∧ 0 ≤ p.2 := by
    have h1 : ∀ᵐ p ∂((gammaMeasure (P.n : ℝ) lam).prod (expMeasure P.s)), 0 ≤ p.1 :=
      ae_of_ae_map measurable_fst.aemeasurable (by rw [Measure.map_fst_prod]; simpa using aeΓ)
    have h2 : ∀ᵐ p ∂((gammaMeasure (P.n : ℝ) lam).prod (expMeasure P.s)), 0 ≤ p.2 :=
      ae_of_ae_map measurable_snd.aemeasurable (by rw [Measure.map_snd_prod]; simpa using aeE)
    exact h1.and h2
  have hprod : Integrable (Function.uncurry fun t τ => phi P d t τ - dTilde P d τ * P.piA)
      ((gammaMeasure (P.n : ℝ) lam).prod (expMeasure P.s)) :=
    Integrable.of_bound hmF.aestronglyMeasurable CF
      (aeprod.mono fun p hp => by
        rw [Real.norm_eq_abs]; exact hF p.1 p.2 hp.1 hp.2)
  have claim3 := integral_integral_swap hprod
  -- claim 4
  have claim4 : ∀ τ, 0 ≤ τ → ∫ t, (phi P d t τ - dTilde P d τ * P.piA) ∂(gammaMeasure (P.n : ℝ) lam)
      = Gm P lam (d + τ) := by
    intro τ hτ
    have hm0 : 0 ≤ min (d + τ) P.T := le_min (by linarith) hT.le
    rw [integral_gamma hn1 hlam]
    have hcongr : ∀ t ∈ Ici (0 : ℝ), pdf' P.n lam t * (phi P d t τ - dTilde P d τ * P.piA)
        = indicator (Iic (min (d + τ) P.T)) (fun t =>
          ((P.T - t) * P.alpha * P.piR - P.piA * (min (d + τ) P.T - t)) * pdf' P.n lam t) t := by
      intro t _
      rw [Fphi_eq]
      unfold indicator
      split_ifs with h1 h2 h2
      · ring
      · exact absurd h1 h2
      · exact absurd h2 h1
      · ring
    rw [setIntegral_congr_fun measurableSet_Ici hcongr, MeasureTheory.integral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ici, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hm0]
    rfl
  -- claim 5
  have claim5 : ∫ τ, Gm P lam (d + τ) ∂(expMeasure P.s) = Sop P.T P.s (Gm P lam) d := by
    have hGc := continuous_Gm_x P lam
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hGc.continuousOn (s := Icc 0 P.T))
    have hbd : ∀ τ, 0 ≤ τ → |Gm P lam (d + τ) - Gm P lam P.T| ≤ 2 * C := by
      intro τ hτ
      have e : Gm P lam (d + τ) = Gm P lam (min (d + τ) P.T) := by
        unfold Gm; rw [min_assoc, min_self]
      have h1 := hC (min (d + τ) P.T) ⟨le_min (by linarith) hT.le, min_le_right _ _⟩
      have h2 := hC P.T ⟨hT.le, le_rfl⟩
      rw [Real.norm_eq_abs] at h1 h2
      rw [e]
      calc |Gm P lam (min (d + τ) P.T) - Gm P lam P.T|
          ≤ |Gm P lam (min (d + τ) P.T)| + |Gm P lam P.T| := abs_sub _ _
        _ ≤ 2 * C := by linarith
    have hpdf1 : ∀ τ, pdf' 1 P.s τ = P.s * exp (-(P.s * τ)) := by
      intro τ; simp [pdf']
    have hint1 := integrableOn_pdf' (n := 1) le_rfl hs
    have hint2 : IntegrableOn (fun τ => (Gm P lam (d + τ) - Gm P lam P.T) * pdf' 1 P.s τ) (Ici 0) :=
      Integrable.bdd_mul hint1 (by fun_prop : Continuous fun τ =>
        Gm P lam (d + τ) - Gm P lam P.T).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun τ hτ => by
          rw [Real.norm_eq_abs]; exact hbd τ hτ))
    have hE1 : ∫ τ, Gm P lam (d + τ) ∂(expMeasure P.s)
        = ∫ τ in Ici 0, pdf' 1 P.s τ * Gm P lam (d + τ) := by
      have := integral_gamma (n := 1) le_rfl hs (fun τ => Gm P lam (d + τ))
      simpa [expMeasure] using this
    have hsplit : ∫ τ in Ici 0, pdf' 1 P.s τ * Gm P lam (d + τ)
        = (∫ τ in Ici 0, (Gm P lam (d + τ) - Gm P lam P.T) * pdf' 1 P.s τ)
          + Gm P lam P.T * ∫ τ in Ici 0, pdf' 1 P.s τ := by
      rw [← MeasureTheory.integral_const_mul, ← integral_add hint2 (hint1.const_mul _)]
      congr 1; ext τ; ring
    have hdiff : ∫ τ in Ici 0, (Gm P lam (d + τ) - Gm P lam P.T) * pdf' 1 P.s τ
        = ∫ τ in (0 : ℝ)..(P.T - d), (Gm P lam (d + τ) - Gm P lam P.T) * pdf' 1 P.s τ := by
      have hcongr : ∀ τ ∈ Ici (0 : ℝ), (Gm P lam (d + τ) - Gm P lam P.T) * pdf' 1 P.s τ
          = indicator (Iic (P.T - d))
            (fun τ => (Gm P lam (d + τ) - Gm P lam P.T) * pdf' 1 P.s τ) τ := by
        intro τ _
        unfold indicator
        split_ifs with h
        · rfl
        · simp only [mem_Iic, not_le] at h
          rw [Gm_of_ge (by linarith)]; ring
      rw [setIntegral_congr_fun measurableSet_Ici hcongr, MeasureTheory.integral_indicator measurableSet_Iic,
        Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ici, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith)]
    have hc1 : Continuous fun τ => Gm P lam (d + τ) * pdf' 1 P.s τ := by
      have := continuous_pdf'_t 1 P.s; fun_prop
    have hc2 : Continuous fun τ => Gm P lam P.T * pdf' 1 P.s τ := by
      have := continuous_pdf'_t 1 P.s; fun_prop
    have hI0 : ∫ τ in (0 : ℝ)..(P.T - d), pdf' 1 P.s τ = 1 - exp (-(P.s * (P.T - d))) := by
      simp_rw [hpdf1]
      rw [intervalIntegral.integral_const_mul, integral_exp_neg_mul hs]
      field_simp
      simp
    have hsub : ∫ τ in (0 : ℝ)..(P.T - d), Gm P lam (d + τ) * pdf' 1 P.s τ
        = P.s * exp (P.s * d) * ∫ x in d..P.T, exp (-(P.s * x)) * Gm P lam x := by
      rw [← intervalIntegral.integral_const_mul]
      have := intervalIntegral.integral_comp_add_left
        (fun x => P.s * exp (P.s * d) * (exp (-(P.s * x)) * Gm P lam x)) d
        (a := 0) (b := P.T - d)
      simp only [add_zero, add_sub_cancel] at this
      rw [← this]
      congr 1; ext τ
      rw [hpdf1]
      have : exp (P.s * d) * exp (-(P.s * (d + τ))) = exp (-(P.s * τ)) := by
        rw [← exp_add]; ring_nf
      linear_combination (-(P.s * Gm P lam (d + τ))) * this
    rw [hE1, hsplit, hdiff, integral_pdf'_Ici le_rfl hs,
      show (fun τ => (Gm P lam (d + τ) - Gm P lam P.T) * pdf' 1 P.s τ)
        = fun τ => Gm P lam (d + τ) * pdf' 1 P.s τ - Gm P lam P.T * pdf' 1 P.s τ by
          ext τ; ring,
      intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hI0, hsub]
    simp only [Sop]
    ring
  rw [claim2, claim3, integral_congr_ae (aeE.mono fun τ hτ => claim4 τ hτ), claim5]
  ring

/-! ## Part A: attainment and the compliant set -/

noncomputable def gS (P : Params) (d lam : ℝ) : ℝ := Sop P.T P.s (Gm P lam) d

lemma n_ge_one {P : Params} (hP : P.Standing) : 1 ≤ P.n := by
  have : (1 : ℝ) < P.n := lt_of_le_of_lt hP.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2
  exact_mod_cast this.le

lemma profit_pos_eq {P : Params} (hP : P.Standing) {d : ℝ} (hd : d ∈ Icc 0 P.T) (θ : ℝ) {μ : ℝ}
    (hμ : 0 < μ) : profit P d θ μ = profitN P d + gS P d μ - θ * μ ^ P.k := by
  unfold profit
  rw [if_neg hμ.ne']
  have := gain_eq hP hd.1 hd.2 hμ
  unfold gS; linarith

lemma continuous_gS (P : Params) : Continuous (fun p : ℝ × ℝ => gS P p.2 p.1) := by
  have hc : Continuous (Function.uncurry fun lam x => exp (-(P.s * x)) * Gm P lam x) := by
    rw [Function.uncurry_def]
    exact (continuous_exp.comp (by fun_prop : Continuous fun p : ℝ × ℝ => -(P.s * p.2))).mul
      (continuous_Gm P)
  have h := intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume)
    (a₀ := P.T) hc
  have hT : Continuous fun p : ℝ × ℝ => Gm P p.1 P.T :=
    (continuous_Gm P).comp (continuous_fst.prodMk continuous_const)
  have hA : Continuous fun p : ℝ × ℝ => P.s * exp (P.s * p.2) := by fun_prop
  have hB : Continuous fun p : ℝ × ℝ => exp (-(P.s * (P.T - p.2))) := by fun_prop
  have := (hA.mul h.neg).add (hB.mul hT)
  refine this.congr fun p => ?_
  simp only [gS, Sop, Pi.add_apply, Pi.mul_apply, Pi.neg_apply]
  rw [intervalIntegral.integral_symm P.T p.2]

lemma gS_le {P : Params} (hP : P.Standing) {d lam : ℝ} (hd : d ∈ Icc 0 P.T) (hlam : 0 < lam) :
    gS P d lam ≤ P.T * P.piR * ∫ t in (0 : ℝ)..P.T, pdf' P.n lam t := by
  have hM : ∀ x ∈ Icc d P.T, Gm P lam x ≤ P.T * P.piR * ∫ t in (0 : ℝ)..P.T, pdf' P.n lam t :=
    fun x hx => Gm_le hP hlam.le (hd.1.trans hx.1)
  have := Sop_le hP.2.2.2.2.2.1 hd.2 (continuous_Gm_x P lam) hM
  have hT := hM P.T ⟨hd.2, le_rfl⟩
  have he := (exp_pos (-(P.s * (P.T - d)))).le
  unfold gS
  nlinarith [mul_nonneg he (sub_nonneg.2 hT)]

set_option maxHeartbeats 1000000 in
lemma attain {P : Params} (hP : P.Standing) {d θ lam : ℝ} (hd : d ∈ Icc 0 P.T) (hθ : 0 < θ)
    (hlam : 0 < lam) (hg : θ * lam ^ P.k ≤ gS P d lam) : θ ∈ compliantTypes P := by
  have hn1 := n_ge_one hP
  have hP' := hP
  obtain ⟨hT, hA, hAR, ha, ha1, hs, hk, hkn⟩ := hP
  set h : ℝ → ℝ := fun μ => gS P d μ - θ * μ ^ P.k with hh
  have hcont : Continuous h := by
    have h1 : Continuous fun μ => gS P d μ :=
      (continuous_gS P).comp (continuous_id.prodMk continuous_const)
    exact h1.sub (continuous_const.mul (Real.continuous_rpow_const (by linarith)))
  suffices H : ∃ μs, 0 < μs ∧ 0 ≤ h μs ∧ ∀ μ, 0 < μ → h μ ≤ h μs by
    obtain ⟨μs, hμs, h0, hmax⟩ := H
    refine ⟨hθ, d, hd, μs, hμs, hμs.le, fun μ hμ => ?_⟩
    rw [profit_pos_eq hP' hd θ hμs]
    rcases hμ.lt_or_eq with hμ' | hμ'
    · rw [profit_pos_eq hP' hd θ hμ']
      have := hmax μ hμ'
      simp only [hh] at this
      linarith
    · rw [← hμ']
      unfold profit
      rw [if_pos rfl]
      simp only [hh] at h0
      linarith
  have hA0 : 0 ≤ P.T * P.piR := by nlinarith
  set A := P.T * P.piR * (P.T ^ P.n / (P.n.factorial : ℝ)) with hAdef
  have hA0' : 0 ≤ A := mul_nonneg hA0 (by positivity)
  have hup1 : ∀ μ, 0 < μ → h μ ≤ P.T * P.piR - θ * μ ^ P.k := by
    intro μ hμ
    have := gS_le hP' hd hμ
    have h1 := int_pdf'_le_one hn1 hμ hT.le
    simp only [hh]; nlinarith
  have hup2 : ∀ μ, 0 < μ → μ ≤ 1 → h μ ≤ A * μ := by
    intro μ hμ hμ1
    have h1 := gS_le hP' hd hμ
    have h2 := int_pdf'_le_pow hn1 hμ.le hT.le
    have h3 : μ ^ P.n ≤ μ := pow_le_of_le_one hμ.le hμ1 (by omega)
    have h4 : 0 ≤ θ * μ ^ P.k := by positivity
    have h5 := mul_le_mul_of_nonneg_left h2 hA0
    have h6 : P.T * P.piR * (μ ^ P.n * P.T ^ P.n / (P.n.factorial : ℝ)) ≤ A * μ := by
      have : μ ^ P.n * P.T ^ P.n / (P.n.factorial : ℝ) ≤ μ * (P.T ^ P.n / (P.n.factorial : ℝ)) := by
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right h3 (by positivity)
      calc _ ≤ P.T * P.piR * (μ * (P.T ^ P.n / (P.n.factorial : ℝ))) :=
            mul_le_mul_of_nonneg_left this hA0
        _ = A * μ := by rw [hAdef]; ring
    simp only [hh]; linarith
  by_cases hcase : ∀ μ, 0 < μ → h μ ≤ h lam
  · exact ⟨lam, hlam, by simp only [hh]; linarith, hcase⟩
  push_neg at hcase
  obtain ⟨μ1, hμ1, hlt⟩ := hcase
  have hc : 0 < h μ1 := lt_of_le_of_lt (by simp only [hh]; linarith) hlt
  set c := h μ1 with hcdef
  set a := min 1 (c / (A + 1)) with ha_def
  set b := max 1 (P.T * P.piR / θ + 1) with hb_def
  have ha0 : 0 < a := lt_min one_pos (by positivity)
  have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
  have hout : ∀ μ, 0 < μ → μ ∉ Icc a b → h μ < c := by
    intro μ hμ hn
    simp only [mem_Icc, not_and_or, not_le] at hn
    rcases hn with hlo | hhi
    · have hμ1' : μ ≤ 1 := hlo.le.trans (min_le_left _ _)
      have h7 := hup2 μ hμ hμ1'
      have hμc : μ < c / (A + 1) := lt_of_lt_of_le hlo (min_le_right _ _)
      have h8 : μ * (A + 1) < c := (lt_div_iff₀ (by linarith)).1 hμc
      nlinarith
    · have hb1 : 1 ≤ μ := (le_max_left _ _).trans hhi.le
      have hb2 : P.T * P.piR / θ < μ := by
        have := lt_of_le_of_lt (le_max_right _ _) hhi; linarith
      have hk' : μ ≤ μ ^ P.k := by
        have := Real.rpow_le_rpow_of_exponent_le hb1 hk
        rwa [Real.rpow_one] at this
      have h9 : P.T * P.piR < θ * μ := by
        have := (div_lt_iff₀ hθ).1 hb2
        linarith
      have := hup1 μ hμ
      nlinarith
  obtain ⟨μs, hμs, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hcont.continuousOn
  have hμ1in : μ1 ∈ Icc a b := by
    by_contra hn
    exact lt_irrefl _ (hout μ1 hμ1 hn)
  have hcs : c ≤ h μs := isMaxOn_iff.1 hmax μ1 hμ1in
  refine ⟨μs, ha0.trans_le hμs.1, by linarith, fun μ hμ => ?_⟩
  by_cases hin : μ ∈ Icc a b
  · exact isMaxOn_iff.1 hmax μ hin
  · linarith [hout μ hμ hin]

lemma mem_CT_iff {P : Params} (hP : P.Standing) {θ : ℝ} :
    θ ∈ compliantTypes P ↔
      0 < θ ∧ ∃ d ∈ Icc 0 P.T, ∃ lam, 0 < lam ∧ θ * lam ^ P.k ≤ gS P d lam := by
  constructor
  · rintro ⟨hθ, d, hd, lam, hlam, -, hopt⟩
    refine ⟨hθ, d, hd, lam, hlam, ?_⟩
    have := hopt 0 le_rfl
    rw [profit_pos_eq hP hd θ hlam] at this
    unfold profit at this
    rw [if_pos rfl] at this
    linarith
  · rintro ⟨hθ, d, hd, lam, hlam, hg⟩
    exact attain hP hd hθ hlam hg

lemma bdd_CT {P : Params} (hP : P.Standing) : BddAbove (compliantTypes P) := by
  have hn1 := n_ge_one hP
  have hP' := hP
  obtain ⟨hT, hA, hAR, ha, ha1, hs, hk, hkn⟩ := hP
  have hA0 : 0 ≤ P.T * P.piR := by nlinarith
  refine ⟨P.T * P.piR * max 1 (P.T ^ P.n / (P.n.factorial : ℝ)), fun θ hθ => ?_⟩
  obtain ⟨hθ0, d, hd, lam, hlam, hg⟩ := (mem_CT_iff hP').1 hθ
  have hg1 := gS_le hP' hd hlam
  rcases le_or_gt 1 lam with h1 | h1
  · have hk1 : 1 ≤ lam ^ P.k := Real.one_le_rpow h1 (by linarith)
    have hI := int_pdf'_le_one hn1 hlam hT.le
    have : θ ≤ P.T * P.piR := by nlinarith [mul_le_mul_of_nonneg_left hI hA0]
    exact this.trans (le_mul_of_one_le_right hA0 (le_max_left _ _))
  · have hkn' : lam ^ (P.n : ℝ) ≤ lam ^ P.k := Real.rpow_le_rpow_of_exponent_ge hlam h1.le hkn.le
    rw [Real.rpow_natCast] at hkn'
    have hI := int_pdf'_le_pow hn1 hlam.le hT.le
    have hpos : 0 < lam ^ P.n := by positivity
    have h2 : θ * lam ^ P.n ≤ P.T * P.piR * (lam ^ P.n * P.T ^ P.n / (P.n.factorial : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hI hA0, mul_le_mul_of_nonneg_left hkn' hθ0.le]
    have h3 : θ ≤ P.T * P.piR * (P.T ^ P.n / (P.n.factorial : ℝ)) := by
      have : θ * lam ^ P.n ≤ (P.T * P.piR * (P.T ^ P.n / (P.n.factorial : ℝ))) * lam ^ P.n := by
        calc θ * lam ^ P.n ≤ _ := h2
          _ = _ := by ring
      exact le_of_mul_le_mul_right this hpos
    exact h3.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hA0)

/-! ## Part B: assembly -/

lemma thetaHat_nonneg (P : Params) : 0 ≤ thetaHat P :=
  Real.sSup_nonneg (fun x hx => hx.1.le)

lemma thetaHat_mono {P P' : Params} (hP' : P'.Standing)
    (h : compliantTypes P ⊆ compliantTypes P') : thetaHat P ≤ thetaHat P' := by
  rcases (compliantTypes P).eq_empty_or_nonempty with he | hne
  · unfold thetaHat; rw [he, Real.sSup_empty]; exact thetaHat_nonneg P'
  · exact csSup_le_csSup (bdd_CT hP') hne h

lemma standing_s {P : Params} (hP : P.Standing) {s₂ : ℝ} (h : P.s ≤ s₂) :
    ({ P with s := s₂ } : Params).Standing := by
  obtain ⟨hT, hA, hAR, ha, ha1, hs, hk, hkn⟩ := hP
  exact ⟨hT, hA, hAR, ha, ha1, lt_of_lt_of_le hs h, hk, hkn⟩

lemma standing_alpha {P : Params} (hP : P.Standing) {α₂ : ℝ} (h : P.alpha ≤ α₂) (h1 : α₂ ≤ 1) :
    ({ P with alpha := α₂ } : Params).Standing := by
  obtain ⟨hT, hA, hAR, ha, ha1, hs, hk, hkn⟩ := hP
  exact ⟨hT, hA, hAR, lt_of_lt_of_le ha h, h1, hs, hk, hkn⟩

lemma exists_max_Sop (T r : ℝ) (hT : 0 ≤ T) {G : ℝ → ℝ} (hG : Continuous G) :
    ∃ y ∈ Icc 0 T, ∀ x ∈ Icc 0 T, Sop T r G x ≤ Sop T r G y := by
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hT)
    (continuous_Sop T r hG).continuousOn
  exact ⟨y, hy, fun x hx => isMaxOn_iff.1 hmax x hx⟩

lemma CT_s_sub {P : Params} (hP : P.Standing) {s₂ : ℝ} (h : P.s ≤ s₂) :
    compliantTypes P ⊆ compliantTypes { P with s := s₂ } := by
  intro θ hθ
  obtain ⟨hθ0, d, hd, lam, hlam, hg⟩ := (mem_CT_iff hP).1 hθ
  have hP' := standing_s hP h
  have hT := hP.1
  have hs := hP.2.2.2.2.2.1
  have hG := continuous_Gm_x P lam
  obtain ⟨y, hy, hmax⟩ := exists_max_Sop P.T s₂ hT.le hG
  have hM : ∀ x ∈ Icc d P.T, Sop P.T s₂ (Gm P lam) x ≤ Sop P.T s₂ (Gm P lam) y :=
    fun x hx => hmax x ⟨hd.1.trans hx.1, hx.2⟩
  have hmix := mixture_le hs h hG hd.2 hM
  have hGT : Gm P lam P.T ≤ Sop P.T s₂ (Gm P lam) y := by
    have := hmax P.T ⟨hT.le, le_rfl⟩; rwa [Sop_T] at this
  have hq : 0 ≤ 1 - P.s / s₂ := by
    rw [sub_nonneg, div_le_one (lt_of_lt_of_le hs h)]; exact h
  have he := (exp_pos (-(P.s * (P.T - d)))).le
  have hnn : 0 ≤ (1 - P.s / s₂) * exp (-(P.s * (P.T - d))) *
      (Sop P.T s₂ (Gm P lam) y - Gm P lam P.T) :=
    mul_nonneg (mul_nonneg hq he) (sub_nonneg.2 hGT)
  refine (mem_CT_iff hP').2 ⟨hθ0, y, hy, lam, hlam, ?_⟩
  have : gS P d lam ≤ Sop P.T s₂ (Gm P lam) y := by unfold gS; linarith
  show θ * lam ^ P.k ≤ Sop P.T s₂ (Gm P lam) y
  exact hg.trans this

lemma Sop_mono {T r : ℝ} (hr : 0 < r) {d : ℝ} (hd : d ≤ T) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfg : ∀ x ∈ Icc d T, f x ≤ g x) : Sop T r f d ≤ Sop T r g d := by
  unfold Sop
  have hint : ∫ x in d..T, exp (-(r * x)) * f x ≤ ∫ x in d..T, exp (-(r * x)) * g x := by
    apply intervalIntegral.integral_mono_on hd
    · exact (by fun_prop : Continuous fun x => exp (-(r * x)) * f x).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun x => exp (-(r * x)) * g x).intervalIntegrable _ _
    · intro x hx
      exact mul_le_mul_of_nonneg_left (hfg x hx) (exp_pos _).le
  have h1 := mul_le_mul_of_nonneg_left hint (mul_pos hr (exp_pos (r * d))).le
  have h2 := mul_le_mul_of_nonneg_left (hfg T ⟨hd, le_rfl⟩) (exp_pos (-(r * (T - d)))).le
  linarith

lemma Sop_const_mul (T r c : ℝ) (f : ℝ → ℝ) (d : ℝ) :
    Sop T r (fun x => c * f x) d = c * Sop T r f d := by
  unfold Sop
  have : (∫ x in d..T, exp (-(r * x)) * (c * f x)) = c * ∫ x in d..T, exp (-(r * x)) * f x := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; ext x; ring
  rw [this]; ring

lemma CT_alpha {P : Params} (hP : P.Standing) {α₂ : ℝ} (h : P.alpha ≤ α₂) (h1 : α₂ ≤ 1) {θ : ℝ}
    (hθ : θ ∈ compliantTypes P) :
    (α₂ / P.alpha) * θ ∈ compliantTypes { P with alpha := α₂ } := by
  obtain ⟨hθ0, d, hd, lam, hlam, hg⟩ := (mem_CT_iff hP).1 hθ
  have hP' := standing_alpha hP h h1
  obtain ⟨hT, hA, hAR, ha, ha1, hs, hk, hkn⟩ := hP
  have hc : 0 < α₂ / P.alpha := div_pos (lt_of_lt_of_le ha h) ha
  refine (mem_CT_iff hP').2 ⟨mul_pos hc hθ0, d, hd, lam, hlam, ?_⟩
  have hmono : Sop P.T P.s (fun x => (α₂ / P.alpha) * Gm P lam x) d ≤
      Sop P.T P.s (Gm { P with alpha := α₂ } lam) d :=
    Sop_mono hs hd.2 (continuous_const.mul (continuous_Gm_x P lam)) (continuous_Gm_x _ lam)
      (fun x hx => Gm_alpha ha hA h hlam.le (hd.1.trans hx.1) hT)
  rw [Sop_const_mul] at hmono
  show α₂ / P.alpha * θ * lam ^ P.k ≤ Sop P.T P.s (Gm { P with alpha := α₂ } lam) d
  calc α₂ / P.alpha * θ * lam ^ P.k = α₂ / P.alpha * (θ * lam ^ P.k) := by ring
    _ ≤ α₂ / P.alpha * gS P d lam := mul_le_mul_of_nonneg_left hg hc.le
    _ ≤ _ := hmono

lemma thetaHat_pos {P : Params} (hP : P.Standing) (hne : (compliantTypes P).Nonempty) :
    0 < thetaHat P := by
  obtain ⟨θ, hθ⟩ := hne
  exact lt_of_lt_of_le hθ.1 (le_csSup (bdd_CT hP) hθ)

lemma thetaHat_alpha {P : Params} (hP : P.Standing) {α₂ : ℝ} (h : P.alpha ≤ α₂) (h1 : α₂ ≤ 1)
    (hne : (compliantTypes P).Nonempty) :
    (α₂ / P.alpha) * thetaHat P ≤ thetaHat { P with alpha := α₂ } := by
  have hP' := standing_alpha hP h h1
  have hc : 0 < α₂ / P.alpha := div_pos (lt_of_lt_of_le hP.2.2.2.1 h) hP.2.2.2.1
  rw [← le_div_iff₀' hc]
  show sSup (compliantTypes P) ≤ _
  apply csSup_le hne
  intro θ hθ
  rw [le_div_iff₀' hc]
  exact le_csSup (bdd_CT hP') (CT_alpha hP h h1 hθ)

lemma theta_hi {P : Params} (hP : P.Standing) {d lam θ : ℝ} (hd : d ∈ Icc 0 P.T) (hlam : 1 ≤ lam)
    (hθ : 0 < θ) (hg : θ * lam ^ P.k ≤ gS P d lam) : θ * lam ≤ P.T * P.piR := by
  have hn1 := n_ge_one hP
  have hl0 : 0 < lam := by linarith
  have h1 := gS_le hP hd hl0
  have h2 := int_pdf'_le_one hn1 hl0 hP.1.le
  have hA0 : 0 ≤ P.T * P.piR := by
    have := hP.1; have := hP.2.1; have := hP.2.2.1; nlinarith
  have hk' : lam ≤ lam ^ P.k := by
    have := Real.rpow_le_rpow_of_exponent_le hlam hP.2.2.2.2.2.2.1
    rwa [Real.rpow_one] at this
  nlinarith [mul_le_mul_of_nonneg_left h2 hA0, mul_le_mul_of_nonneg_left hk' hθ.le]

lemma theta_lo {P : Params} (hP : P.Standing) {d lam θ : ℝ} (hd : d ∈ Icc 0 P.T) (hlam : 0 < lam)
    (hg : θ * lam ^ P.k ≤ gS P d lam) :
    θ ≤ P.T * P.piR * (P.T ^ P.n / (P.n.factorial : ℝ)) * lam ^ ((P.n : ℝ) - P.k) := by
  have hn1 := n_ge_one hP
  have h1 := gS_le hP hd hlam
  have h2 := int_pdf'_le_pow hn1 hlam.le hP.1.le
  have hA0 : 0 ≤ P.T * P.piR := by
    have := hP.1; have := hP.2.1; have := hP.2.2.1; nlinarith
  have hsplit : lam ^ P.n = lam ^ P.k * lam ^ ((P.n : ℝ) - P.k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hlam]; congr 1; ring
  have hk0 : 0 < lam ^ P.k := Real.rpow_pos_of_pos hlam _
  have h3 : θ * lam ^ P.k ≤ (P.T * P.piR * (P.T ^ P.n / (P.n.factorial : ℝ)) *
      lam ^ ((P.n : ℝ) - P.k)) * lam ^ P.k := by
    have := mul_le_mul_of_nonneg_left h2 hA0
    calc θ * lam ^ P.k ≤ gS P d lam := hg
      _ ≤ P.T * P.piR * (lam ^ P.n * P.T ^ P.n / (P.n.factorial : ℝ)) := h1.trans this
      _ = _ := by rw [hsplit]; ring
  exact le_of_mul_le_mul_right h3 hk0

set_option maxHeartbeats 1000000 in
lemma thetaHat_s_strict {P : Params} (hP : P.Standing) (hne : (compliantTypes P).Nonempty)
    {s₂ : ℝ} (h : P.s < s₂) : thetaHat P < thetaHat { P with s := s₂ } := by
  have hP' := standing_s hP h.le
  have hθpos := thetaHat_pos hP hne
  obtain ⟨θ0, hθ0def⟩ : ∃ θ0 : ℝ, θ0 = thetaHat P := ⟨_, rfl⟩
  rw [← hθ0def] at hθpos ⊢
  have hT := hP.1
  have hs := hP.2.2.2.2.2.1
  have hk := hP.2.2.2.2.2.2.1
  have hkn := hP.2.2.2.2.2.2.2
  have hA0 : 0 ≤ P.T * P.piR := by
    have := hP.2.1; have := hP.2.2.1; nlinarith
  obtain ⟨C1, hC1def⟩ : ∃ C1 : ℝ, C1 = P.T * P.piR := ⟨_, rfl⟩
  obtain ⟨C2, hC2def⟩ : ∃ C2 : ℝ, C2 = P.T * P.piR * (P.T ^ P.n / (P.n.factorial : ℝ)) :=
    ⟨_, rfl⟩
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = (P.n : ℝ) - P.k := ⟨_, rfl⟩
  have hC2 : 0 ≤ C2 := by rw [hC2def]; exact mul_nonneg hA0 (by positivity)
  have he0 : 0 < e := by rw [hedef]; linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = θ0 / (2 * (C2 + 1)) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hq1 : (C2 + 1) * q = θ0 / 2 := by
    rw [hqdef]; field_simp
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = min 1 (q ^ e⁻¹) := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = max 1 (2 * C1 / θ0 + 1) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [hadef]; exact lt_min one_pos (Real.rpow_pos_of_pos hq0 _)
  have hab : a ≤ b := by
    rw [hadef, hbdef]; exact (min_le_left _ _).trans (le_max_left _ _)
  have hout : ∀ θ d lam, d ∈ Icc 0 P.T → 0 < lam → 0 < θ → θ * lam ^ P.k ≤ gS P d lam →
      lam ∉ Icc a b → θ < θ0 / 2 := by
    intro θ d lam hd hlam hθ hg hn
    simp only [mem_Icc, not_and_or, not_le] at hn
    rcases hn with hlo | hhi
    · have h1 := theta_lo hP hd hlam hg
      rw [← hC2def, ← hedef] at h1
      have h2 : lam ^ e < q := by
        have hla : lam < q ^ e⁻¹ := by
          have := min_le_right 1 (q ^ e⁻¹); rw [← hadef] at this; linarith
        have := Real.rpow_lt_rpow hlam.le hla he0
        rwa [Real.rpow_inv_rpow hq0.le he0.ne'] at this
      nlinarith [mul_le_mul_of_nonneg_left h2.le hC2]
    · have hb1 : 1 ≤ lam := by
        have := le_max_left 1 (2 * C1 / θ0 + 1); rw [← hbdef] at this; linarith
      have h1 := theta_hi hP hd hb1 hθ hg
      rw [← hC1def] at h1
      have hb2 : 2 * C1 / θ0 < lam := by
        have := le_max_right 1 (2 * C1 / θ0 + 1); rw [← hbdef] at this; linarith
      have hb3 : 2 * C1 < θ0 * lam := by
        have := (div_lt_iff₀ hθpos).1 hb2; linarith
      nlinarith
  have hK : IsCompact (Icc a b ×ˢ Icc 0 P.T) := isCompact_Icc.prod isCompact_Icc
  have hKne : (Icc a b ×ˢ Icc 0 P.T).Nonempty :=
    ⟨(a, 0), ⟨left_mem_Icc.2 hab, left_mem_Icc.2 hT.le⟩⟩
  have hpowc : Continuous fun p : ℝ × ℝ => p.1 ^ P.k :=
    (Real.continuous_rpow_const (by linarith)).comp continuous_fst
  have hFc : ContinuousOn (fun p : ℝ × ℝ => gS P p.2 p.1 / p.1 ^ P.k) (Icc a b ×ˢ Icc 0 P.T) := by
    apply ContinuousOn.div (continuous_gS P).continuousOn hpowc.continuousOn
    intro p hp
    exact (Real.rpow_pos_of_pos (ha0.trans_le hp.1.1) _).ne'
  obtain ⟨⟨lam, d⟩, hpK, hmax⟩ := hK.exists_isMaxOn hKne hFc
  have hlamab : lam ∈ Icc a b := hpK.1
  have hd : d ∈ Icc 0 P.T := hpK.2
  have hlam0 : 0 < lam := ha0.trans_le hlamab.1
  have hF : θ0 ≤ gS P d lam / lam ^ P.k := by
    have hle : sSup (compliantTypes P) ≤ max (θ0 / 2) (gS P d lam / lam ^ P.k) := by
      apply csSup_le hne
      intro θ hθ
      obtain ⟨hθ0', d', hd', lam', hlam', hg'⟩ := (mem_CT_iff hP).1 hθ
      by_cases hin : lam' ∈ Icc a b
      · apply le_max_of_le_right
        have h1 : θ ≤ gS P d' lam' / lam' ^ P.k := by
          rw [le_div_iff₀ (Real.rpow_pos_of_pos hlam' _)]; exact hg'
        have h2 := isMaxOn_iff.1 hmax (lam', d') ⟨hin, hd'⟩
        dsimp only at h2
        exact h1.trans h2
      · exact le_max_of_le_left (hout θ d' lam' hd' hlam' hθ0' hg' hin).le
    have hle' : θ0 ≤ max (θ0 / 2) (gS P d lam / lam ^ P.k) := (le_of_eq hθ0def).trans hle
    rcases le_max_iff.1 hle' with h' | h'
    · linarith
    · exact h'
  have hG := continuous_Gm_x P lam
  obtain ⟨y, hy, hymax⟩ := exists_max_Sop P.T s₂ hT.le hG
  obtain ⟨δ, hδ, hnear⟩ := Gm_near_T hP hlam0
  have hy0 : max 0 (P.T - δ / 2) < P.T := max_lt hT (by linarith)
  have hgt : Gm P lam P.T < Sop P.T s₂ (Gm P lam) (max 0 (P.T - δ / 2)) :=
    Sop_gt_T (hs.trans h) hG hy0 (fun x hx => hnear x
      ⟨by linarith [le_max_right 0 (P.T - δ / 2), hx.1], hx.2⟩)
  have hMgt : Gm P lam P.T < Sop P.T s₂ (Gm P lam) y :=
    hgt.trans_le (hymax _ ⟨le_max_left _ _, hy0.le⟩)
  have hM : ∀ x ∈ Icc d P.T, Sop P.T s₂ (Gm P lam) x ≤ Sop P.T s₂ (Gm P lam) y :=
    fun x hx => hymax x ⟨hd.1.trans hx.1, hx.2⟩
  have hmix := mixture_le hs h.le hG hd.2 hM
  have hq : 0 < 1 - P.s / s₂ := by
    rw [sub_pos, div_lt_one (hs.trans h)]; exact h
  have hpos : 0 < (1 - P.s / s₂) * exp (-(P.s * (P.T - d))) *
      (Sop P.T s₂ (Gm P lam) y - Gm P lam P.T) :=
    mul_pos (mul_pos hq (exp_pos _)) (sub_pos.2 hMgt)
  have hlt : gS P d lam < Sop P.T s₂ (Gm P lam) y := by unfold gS; linarith
  have hk0 : 0 < lam ^ P.k := Real.rpow_pos_of_pos hlam0 _
  have hlt2 : gS P d lam / lam ^ P.k < Sop P.T s₂ (Gm P lam) y / lam ^ P.k :=
    (div_lt_div_iff_of_pos_right hk0).2 hlt
  have hmem : Sop P.T s₂ (Gm P lam) y / lam ^ P.k ∈ compliantTypes { P with s := s₂ } := by
    refine (mem_CT_iff hP').2 ⟨hθpos.trans_le (hF.trans hlt2.le), y, hy, lam, hlam0, ?_⟩
    show Sop P.T s₂ (Gm P lam) y / lam ^ P.k * lam ^ P.k ≤ Sop P.T s₂ (Gm P lam) y
    rw [div_mul_cancel₀ _ hk0.ne']
  calc θ0 ≤ gS P d lam / lam ^ P.k := hF
    _ < _ := hlt2
    _ ≤ thetaHat { P with s := s₂ } := le_csSup (bdd_CT hP') hmem

end PMC1023

open PMC1023

open PostmarketCompliance.Threshold in
theorem solution (P : Params) (hP : P.Standing) :
    (∀ s₂ : ℝ, P.s ≤ s₂ →
      thetaHat P ≤ thetaHat { P with s := s₂ }) ∧
    (∀ α₂ : ℝ, P.alpha ≤ α₂ → α₂ ≤ 1 →
      thetaHat P ≤ thetaHat { P with alpha := α₂ }) ∧
    ((compliantTypes P).Nonempty →
      (∀ s₂ : ℝ, P.s < s₂ →
        thetaHat P < thetaHat { P with s := s₂ }) ∧
      (∀ α₂ : ℝ, P.alpha < α₂ → α₂ ≤ 1 →
        thetaHat P < thetaHat { P with alpha := α₂ })) := by
  refine ⟨fun s₂ h => thetaHat_mono (standing_s hP h) (CT_s_sub hP h), fun α₂ h h1 => ?_,
    fun hne => ⟨fun s₂ h => thetaHat_s_strict hP hne h, fun α₂ h h1 => ?_⟩⟩
  · rcases (compliantTypes P).eq_empty_or_nonempty with he | hne
    · unfold thetaHat; rw [he, Real.sSup_empty]; exact thetaHat_nonneg _
    · have h2 := thetaHat_alpha hP h h1 hne
      have h3 := thetaHat_nonneg P
      have hc : 1 ≤ α₂ / P.alpha := (one_le_div hP.2.2.2.1).2 h
      nlinarith
  · have h2 := thetaHat_alpha hP h.le h1 hne
    have h3 := thetaHat_pos hP hne
    have hc : 1 < α₂ / P.alpha := (one_lt_div hP.2.2.2.1).2 h
    nlinarith
