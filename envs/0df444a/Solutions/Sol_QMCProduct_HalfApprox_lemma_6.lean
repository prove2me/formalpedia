-- Prove2me | solution 1 for QMCProduct.HalfApprox.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T10:33:08.32374+00:00
-- url     : https://prove2.me/submissions/fa0febbf-a5c5-482b-b137-dc1c0f583146

import Definitions.Def_QMCProduct_HalfApprox_Algorithm
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false

open QMCProduct.HalfApprox

namespace QMCLemma6Aux

/-- Real hypergeometric coefficient. -/
noncomputable abbrev cf (a b c : ℝ) (n : ℕ) : ℝ := ordinaryHypergeometricCoefficient a b c n

lemma cf_nonneg (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (n : ℕ) : 0 ≤ cf a b c n := by
  unfold cf ordinaryHypergeometricCoefficient
  have h1 := ascPochhammer_pos n a ha
  have h2 := ascPochhammer_pos n b hb
  have h3 := ascPochhammer_pos n c hc
  positivity

lemma hyp_eq_tsum (a b c x : ℝ) :
    ordinaryHypergeometric a b c x = ∑' n : ℕ, cf a b c n * x ^ n := by
  rw [ordinaryHypergeometric_eq_tsum]
  rfl

lemma hyp_summable (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : |x| < 1) :
    Summable (fun n : ℕ => cf a b c n * x ^ n) := by
  have hr : (ordinaryHypergeometricSeries ℝ a b c).radius = 1 := by
    apply ordinaryHypergeometricSeries_radius_eq_one
    intro kn
    have : (0 : ℝ) ≤ kn := Nat.cast_nonneg kn
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> linarith
  have hmem : x ∈ Metric.eball (0 : ℝ) (ordinaryHypergeometricSeries ℝ a b c).radius := by
    rw [hr, Metric.mem_eball, edist_zero_right]
    have : (‖x‖₊ : ENNReal) < 1 := by
      rw [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe]
      simpa using hx
    exact this
  have hs := (ordinaryHypergeometricSeries ℝ a b c).summable_norm_apply hmem
  refine Summable.of_norm ?_
  refine hs.congr (fun n => ?_)
  rw [ordinaryHypergeometricSeries_apply_eq]
  rfl

lemma cf_shift (n : ℕ) :
    ((n : ℝ) + 1) * cf (1 / 2) (1 / 2) (5 / 2) (n + 1) =
      (1 / 10) * cf (3 / 2) (3 / 2) (7 / 2) n := by
  unfold cf ordinaryHypergeometricCoefficient
  have key : ∀ a : ℝ, (ascPochhammer ℝ (n + 1)).eval a = a * (ascPochhammer ℝ n).eval (a + 1) := by
    intro a
    rw [ascPochhammer_succ_left]
    simp [Polynomial.eval_comp]
  simp only [key]
  rw [Nat.factorial_succ]
  have e1 : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
  have e2 : (5 / 2 : ℝ) + 1 = 7 / 2 := by norm_num
  rw [e1, e2]
  have hc := ascPochhammer_pos n (7 / 2 : ℝ) (by norm_num)
  have hf : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  push_cast
  field_simp
  ring

lemma F3_eq (t : ℝ) :
    F 3 t = 8 / (3 * Real.pi) * t * ordinaryHypergeometric (1 / 2 : ℝ) (1 / 2 : ℝ) (5 / 2 : ℝ) (t ^ 2) := by
  unfold F
  have h1 : (((3 : ℕ) : ℝ) + 1) / 2 = 2 := by norm_num
  have h2 : ((3 : ℕ) : ℝ) / 2 = 1 / 2 + 1 := by norm_num
  have h3 : ((3 : ℕ) : ℝ) / 2 + 1 = 5 / 2 := by norm_num
  rw [h1, h3, h2, Real.Gamma_two, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  have hs0 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  push_cast
  field_simp
  rw [hs]
  ring

/-- Tangent-line inequality for odd powers, from Bernoulli. -/
lemma pow_tangent (γ v : ℝ) (hγ : 0 < γ) (hv : -γ ≤ v) (n : ℕ) :
    γ ^ (2 * n + 1) + ((2 * n + 1 : ℕ) : ℝ) * γ ^ (2 * n) * (v - γ) ≤ v ^ (2 * n + 1) := by
  have hb := one_add_mul_le_pow (a := v / γ - 1) (by
    have : -1 ≤ v / γ := by rw [le_div_iff₀ hγ]; linarith
    linarith) (2 * n + 1)
  have e : 1 + (v / γ - 1) = v / γ := by ring
  rw [e, div_pow] at hb
  have hg : 0 < γ ^ (2 * n + 1) := pow_pos hγ _
  have := mul_le_mul_of_nonneg_left hb hg.le
  rw [mul_div_cancel₀ _ hg.ne'] at this
  calc γ ^ (2 * n + 1) + ((2 * n + 1 : ℕ) : ℝ) * γ ^ (2 * n) * (v - γ)
      = γ ^ (2 * n + 1) * (1 + ((2 * n + 1 : ℕ) : ℝ) * (v / γ - 1)) := by
        rw [pow_succ]; field_simp
    _ ≤ v ^ (2 * n + 1) := this

end QMCLemma6Aux

open QMCLemma6Aux in
theorem solution (γ : ℝ) (hγ1 : 1 / 3 ≤ γ) (hγ2 : γ < 1)
    (hh : ∀ v ∈ Set.Ioc (-(1 / 3 : ℝ)) γ, hLemma6 v γ < 0)
    (hg : (1 / 2 : ℝ) ≤ (1 + F 3 γ) / (1 + 3 * γ)) :
    ∀ v ∈ Set.Ioc (-(1 / 3 : ℝ)) γ, (1 / 2 : ℝ) ≤ (1 + F 3 v) / (1 + 3 * v) := by
  intro v hv
  obtain ⟨hv1, hv2⟩ := hv
  have hγ0 : 0 < γ := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  set z : ℝ := γ ^ 2 with hz
  have hz0 : 0 ≤ z := by positivity
  have hz1 : |z| < 1 := by
    rw [abs_of_nonneg hz0]; nlinarith
  have hvz : |v ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg v)]; nlinarith
  -- coefficients
  set a : ℕ → ℝ := cf (1 / 2) (1 / 2) (5 / 2) with ha_def
  set b : ℕ → ℝ := cf (3 / 2) (3 / 2) (7 / 2) with hb_def
  have ha0 : ∀ n, 0 ≤ a n := fun n => cf_nonneg _ _ _ (by norm_num) (by norm_num) (by norm_num) n
  have sa : Summable (fun n => a n * z ^ n) :=
    hyp_summable _ _ _ _ (by norm_num) (by norm_num) (by norm_num) hz1
  have sb : Summable (fun n => b n * z ^ n) :=
    hyp_summable _ _ _ _ (by norm_num) (by norm_num) (by norm_num) hz1
  have sav : Summable (fun n => a n * (v ^ 2) ^ n) :=
    hyp_summable _ _ _ _ (by norm_num) (by norm_num) (by norm_num) hvz
  set S1 : ℝ := ∑' n, a n * z ^ n with hS1
  set S2 : ℝ := ∑' n, b n * z ^ n with hS2
  have hf1 : ordinaryHypergeometric (1 / 2 : ℝ) (1 / 2 : ℝ) (5 / 2 : ℝ) z = S1 := hyp_eq_tsum _ _ _ _
  have hf2 : ordinaryHypergeometric (3 / 2 : ℝ) (3 / 2 : ℝ) (7 / 2 : ℝ) z = S2 := hyp_eq_tsum _ _ _ _
  -- the derivative series
  set u : ℕ → ℝ := fun n => a n * ((2 * n + 1 : ℕ) : ℝ) * γ ^ (2 * n) with hu
  have hshift : ∀ n, (fun m : ℕ => 2 * ((m : ℝ) * a m * z ^ m)) (n + 1) = z / 5 * (b n * z ^ n) := by
    intro n
    have := cf_shift n
    simp only
    push_cast
    rw [pow_succ]
    have : ((n : ℝ) + 1) * a (n + 1) = 1 / 10 * b n := this
    linear_combination (2 * z ^ n * z) * this
  have sd : Summable (fun m : ℕ => 2 * ((m : ℝ) * a m * z ^ m)) := by
    rw [← summable_nat_add_iff 1]
    simp_rw [hshift]
    exact sb.mul_left _
  have hdsum : ∑' m : ℕ, 2 * ((m : ℝ) * a m * z ^ m) = z / 5 * S2 := by
    rw [sd.tsum_eq_zero_add]
    simp_rw [hshift]
    simp [tsum_mul_left, hS2]
  have hu_eq : ∀ n, u n = a n * z ^ n + 2 * ((n : ℝ) * a n * z ^ n) := by
    intro n
    simp only [hu, hz]
    push_cast
    rw [pow_mul]
    ring
  have su : Summable u := by
    have := sa.add sd
    refine this.congr (fun n => (hu_eq n).symm)
  have hU : ∑' n, u n = S1 + z / 5 * S2 := by
    rw [tsum_congr hu_eq, sa.tsum_add sd, hdsum]
  -- odd series at v and γ
  have hoddv : ∑' n, a n * v ^ (2 * n + 1) = v * ∑' n, a n * (v ^ 2) ^ n := by
    rw [← tsum_mul_left]
    congr 1; funext n; rw [← pow_mul, pow_succ]; ring
  have soddv : Summable (fun n => a n * v ^ (2 * n + 1)) := by
    refine (sav.mul_left v).congr (fun n => ?_)
    rw [← pow_mul, pow_succ]; ring
  have soddg : Summable (fun n => a n * γ ^ (2 * n + 1)) := by
    refine (sa.mul_left γ).congr (fun n => ?_)
    simp only [hz]
    rw [← pow_mul, pow_succ]; ring
  have hoddg : ∑' n, a n * γ ^ (2 * n + 1) = γ * S1 := by
    rw [hS1, ← tsum_mul_left]
    congr 1; funext n; simp only [hz]; rw [← pow_mul, pow_succ]; ring
  -- main tangent inequality
  have htan : γ * S1 + (v - γ) * (S1 + z / 5 * S2) ≤ ∑' n, a n * v ^ (2 * n + 1) := by
    rw [← hoddg, ← hU, ← tsum_mul_left, ← soddg.tsum_add (su.mul_left _)]
    refine Summable.tsum_le_tsum (fun n => ?_) (soddg.add (su.mul_left _)) soddv
    have ht := pow_tangent γ v hγ0 (by linarith) n
    have := mul_le_mul_of_nonneg_left ht (ha0 n)
    simp only [hu]
    linarith
  -- rewrite F
  have hFv : F 3 v = 8 / (3 * Real.pi) * ∑' n, a n * v ^ (2 * n + 1) := by
    rw [F3_eq, hoddv, hyp_eq_tsum]; ring
  have hFg : F 3 γ = 8 / (3 * Real.pi) * (γ * S1) := by
    rw [F3_eq, ← hf1]; ring
  -- the hypothesis at v = γ
  have hhγ := hh γ ⟨by linarith, le_refl γ⟩
  unfold hLemma6 at hhγ
  rw [← hz, hf1, hf2] at hhγ
  have hden : 0 < 15 * Real.pi * (3 * γ + 1) ^ 2 := by positivity
  have hnum : 8 * (3 * γ + 1) * z * S2 + 40 * S1 - 45 * Real.pi < 0 := by
    have := (div_neg_iff.mp hhγ)
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · exact h
  -- conclude
  have h3v : 0 < 1 + 3 * v := by linarith
  have h3g : 0 < 1 + 3 * γ := by linarith
  rw [hFg, le_div_iff₀ h3g] at hg
  rw [hFv, le_div_iff₀ h3v]
  set T := ∑' n, a n * v ^ (2 * n + 1)
  set C := 8 / (3 * Real.pi) with hC
  have hC0 : 0 < C := by positivity
  have hCpi : C * Real.pi = 8 / 3 := by rw [hC]; field_simp
  have hD : C * (S1 + z / 5 * S2) * (1 + 3 * γ) < 3 * (1 + C * (γ * S1)) := by
    have hX : C * (8 * (3 * γ + 1) * z * S2 + 40 * S1 - 45 * Real.pi) < 0 :=
      mul_neg_of_pos_of_neg hC0 hnum
    have e : 3 * (1 + C * (γ * S1)) - C * (S1 + z / 5 * S2) * (1 + 3 * γ) =
        -(1 / 40) * (C * (8 * (3 * γ + 1) * z * S2 + 40 * S1 - 45 * Real.pi)) := by
      linear_combination (-9 / 8 : ℝ) * hCpi
    linarith
  have hvg : v - γ ≤ 0 := by linarith
  have h1 : C * (γ * S1 + (v - γ) * (S1 + z / 5 * S2)) ≤ C * T :=
    mul_le_mul_of_nonneg_left htan hC0.le
  have s1 : (1 + C * (γ * S1 + (v - γ) * (S1 + z / 5 * S2))) * (1 + 3 * γ) ≤
      (1 + C * T) * (1 + 3 * γ) := mul_le_mul_of_nonneg_right (by linarith) h3g.le
  have s2 : (v - γ) * (3 * (1 + C * (γ * S1))) ≤ (v - γ) * (C * (S1 + z / 5 * S2) * (1 + 3 * γ)) :=
    mul_le_mul_of_nonpos_left hD.le hvg
  have e1 : (1 + C * (γ * S1 + (v - γ) * (S1 + z / 5 * S2))) * (1 + 3 * γ) =
      (1 + C * (γ * S1)) * (1 + 3 * γ) + (v - γ) * (C * (S1 + z / 5 * S2) * (1 + 3 * γ)) := by ring
  have e2 : (1 + C * (γ * S1)) * (1 + 3 * v) =
      (1 + C * (γ * S1)) * (1 + 3 * γ) + (v - γ) * (3 * (1 + C * (γ * S1))) := by ring
  have key : (1 + C * (γ * S1)) * (1 + 3 * v) ≤ (1 + C * T) * (1 + 3 * γ) := by
    rw [e2]; rw [e1] at s1; linarith
  have s3 : 1 / 2 * (1 + 3 * γ) * (1 + 3 * v) ≤ (1 + C * (γ * S1)) * (1 + 3 * v) :=
    mul_le_mul_of_nonneg_right hg h3v.le
  have k2 : 1 / 2 * (1 + 3 * v) * (1 + 3 * γ) ≤ (1 + C * T) * (1 + 3 * γ) := by
    have e3 : 1 / 2 * (1 + 3 * v) * (1 + 3 * γ) = 1 / 2 * (1 + 3 * γ) * (1 + 3 * v) := by ring
    rw [e3]; exact s3.trans key
  exact le_of_mul_le_mul_right k2 h3g
