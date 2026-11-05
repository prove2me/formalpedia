-- Prove2me | solution 1 for StrongConv.tfae_extends_csDistribution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T23:41:11.665426+00:00
-- url     : https://prove2.me/submissions/737c0102-692b-4b58-b271-7e898407375c

import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_cNorm_iteratedDeriv_le
import Mathlib

section
section
open Polynomial

namespace StrongConvS4
open StrongConv

/-- `T_j(x / K)`. -/
noncomputable def cheb (K : ℝ) (j : ℕ) : ℝ[X] := (Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X)

/-- Chebyshev (cosine) coefficient `j` of `φ` on `[-K, K]`. -/
noncomputable def coef (K : ℝ) (φ : ℝ → ℝ) (j : ℕ) : ℝ :=
  (if j = 0 then 1 / (2 * Real.pi) else 1 / Real.pi) *
    ∫ θ in (0 : ℝ)..2 * Real.pi, φ (K * Real.cos θ) * Real.cos (j * θ)

end StrongConvS4

end
end

section
section
open Polynomial

namespace StrongConvS4.PartF
open StrongConvS4 StrongConv

lemma pf_per_deriv (G : ℝ → ℝ) (hG : ∀ θ, G (θ + 2 * Real.pi) = G θ) (θ : ℝ) :
    deriv G (θ + 2 * Real.pi) = deriv G θ := by
  have h : (fun x => G (x + 2 * Real.pi)) = G := funext hG
  have := deriv_comp_add_const (f := G) (a := 2 * Real.pi) (x := θ)
  rw [h] at this
  exact this.symm

lemma pf_decay_aux (k : ℕ) : ∀ (G : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) G → (∀ θ, G (θ + 2 * Real.pi) = G θ) →
    ∀ B : ℝ, (∀ θ, |iteratedDeriv k G θ| ≤ B) → ∀ j : ℕ, 1 ≤ j →
    |∫ θ in (0 : ℝ)..2 * Real.pi, G θ * Real.cos (j * θ)| ≤ 2 * Real.pi * B / (j : ℝ) ^ k ∧
    |∫ θ in (0 : ℝ)..2 * Real.pi, G θ * Real.sin (j * θ)| ≤ 2 * Real.pi * B / (j : ℝ) ^ k := by
  induction k with
  | zero =>
    intro G hG _ B hB j hj
    have hB' : ∀ θ, |G θ| ≤ B := fun θ => by simpa using hB θ
    have two : (0:ℝ) ≤ 2 * Real.pi := by positivity
    constructor
    · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
        (f := fun θ => G θ * Real.cos (j * θ)) (C := B) (fun x _ => by
          rw [Real.norm_eq_abs, abs_mul]
          calc |G x| * |Real.cos (j * x)| ≤ B * 1 :=
                mul_le_mul (hB' x) (Real.abs_cos_le_one _) (abs_nonneg _) ((abs_nonneg _).trans (hB' x))
            _ = B := mul_one _)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * Real.pi - 0)] at this
      simpa [mul_comm] using this
    · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
        (f := fun θ => G θ * Real.sin (j * θ)) (C := B) (fun x _ => by
          rw [Real.norm_eq_abs, abs_mul]
          calc |G x| * |Real.sin (j * x)| ≤ B * 1 :=
                mul_le_mul (hB' x) (Real.abs_sin_le_one _) (abs_nonneg _) ((abs_nonneg _).trans (hB' x))
            _ = B := mul_one _)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * Real.pi - 0)] at this
      simpa [mul_comm] using this
  | succ k ih =>
    intro G hG hper B hB j hj
    have hGs : ContDiff ℝ (⊤ : ℕ∞) (deriv G) := by
      exact (contDiff_infty_iff_deriv.mp hG).2
    have hper' : ∀ θ, deriv G (θ + 2 * Real.pi) = deriv G θ := pf_per_deriv G hper
    have hB' : ∀ θ, |iteratedDeriv k (deriv G) θ| ≤ B := fun θ => by
      rw [← iteratedDeriv_succ']; exact hB θ
    obtain ⟨ihc, ihs⟩ := ih (deriv G) hGs hper' B hB' j hj
    have hjpos : (0:ℝ) < j := by exact_mod_cast hj
    have hGd : ∀ x, HasDerivAt G (deriv G x) x := fun x =>
      ((hG.differentiable (by simp)) x).hasDerivAt
    have hGc : Continuous G := hG.continuous
    have hG'c : Continuous (deriv G) := hGs.continuous
    have e0 : G (2 * Real.pi) = G 0 := by simpa using hper 0
    have hjne : (j:ℝ) ≠ 0 := hjpos.ne'
    have hpow : (0:ℝ) < (j:ℝ) ^ k := by positivity
    have hsin2 : Real.sin (j * (2 * Real.pi)) = 0 := by
      have := Real.sin_nat_mul_pi (2 * j)
      rw [show ((2 * j : ℕ) : ℝ) * Real.pi = j * (2 * Real.pi) by push_cast; ring] at this
      exact this
    have hcos2 : Real.cos (j * (2 * Real.pi)) = 1 := by
      have := Real.cos_nat_mul_two_pi j
      rw [show (j:ℝ) * (2 * Real.pi) = j * (2 * Real.pi) from rfl] at this
      exact this
    -- integrate by parts, cos kernel
    have I1 : ∫ θ in (0 : ℝ)..2 * Real.pi, G θ * Real.cos (j * θ)
        = -(1 / j) * ∫ θ in (0 : ℝ)..2 * Real.pi, deriv G θ * Real.sin (j * θ) := by
      have := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * Real.pi)
        (u := G) (u' := deriv G) (v := fun θ => Real.sin (j * θ) / j) (v' := fun θ => Real.cos (j * θ))
        (fun x _ => hGd x)
        (fun x _ => by
          have := ((Real.hasDerivAt_sin (j * x)).comp x ((hasDerivAt_id x).const_mul (j:ℝ))).div_const (j:ℝ)
          convert this using 1
          simp; field_simp)
        (hG'c.intervalIntegrable _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
      rw [this]
      simp only [hsin2, Real.sin_zero, mul_zero, zero_div, sub_zero, mul_zero]
      rw [show ∫ x in (0:ℝ)..2 * Real.pi, deriv G x * (Real.sin (j * x) / j)
          = 1 / j * ∫ θ in (0 : ℝ)..2 * Real.pi, deriv G θ * Real.sin (j * θ) from by
        rw [← intervalIntegral.integral_const_mul]; congr 1; ext θ; ring]
      ring
    have I2 : ∫ θ in (0 : ℝ)..2 * Real.pi, G θ * Real.sin (j * θ)
        = (1 / j) * ∫ θ in (0 : ℝ)..2 * Real.pi, deriv G θ * Real.cos (j * θ) := by
      have := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * Real.pi)
        (u := G) (u' := deriv G) (v := fun θ => -Real.cos (j * θ) / j) (v' := fun θ => Real.sin (j * θ))
        (fun x _ => hGd x)
        (fun x _ => by
          have := (((Real.hasDerivAt_cos (j * x)).comp x ((hasDerivAt_id x).const_mul (j:ℝ))).neg).div_const (j:ℝ)
          convert this using 1
          simp; field_simp)
        (hG'c.intervalIntegrable _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
      rw [this]
      simp only [hcos2, Real.cos_zero, mul_zero, e0]
      rw [← intervalIntegral.integral_const_mul]
      have : ∀ θ, deriv G θ * (-Real.cos (j * θ) / j) = -(1 / j * (deriv G θ * Real.cos (j * θ))) := by
        intro θ; field_simp
      simp only [this, intervalIntegral.integral_neg]
      field_simp; ring
    have key : ∀ A : ℝ, |A| ≤ 2 * Real.pi * B / (j:ℝ)^k →
        |(1 / (j:ℝ)) * A| ≤ 2 * Real.pi * B / (j:ℝ)^(k+1) := by
      intro A hA
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / j), pow_succ]
      calc 1 / (j:ℝ) * |A| ≤ 1 / (j:ℝ) * (2 * Real.pi * B / (j:ℝ)^k) :=
            mul_le_mul_of_nonneg_left hA (by positivity)
        _ = _ := by field_simp
    constructor
    · rw [I1, neg_mul, abs_neg]; exact key _ ihs
    · rw [I2]; exact key _ ihc

theorem coef_decay (K : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (k : ℕ) (B : ℝ)
    (hB : ∀ θ : ℝ, |iteratedDeriv k (fun θ => φ (K * Real.cos θ)) θ| ≤ B) (j : ℕ) (hj : 1 ≤ j) :
    |coef K φ j| ≤ 2 * B / (j : ℝ) ^ k := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun θ => φ (K * Real.cos θ)) :=
    hφ.comp (contDiff_const.mul Real.contDiff_cos)
  have hper : ∀ θ, (fun θ => φ (K * Real.cos θ)) (θ + 2 * Real.pi) = (fun θ => φ (K * Real.cos θ)) θ := by
    intro θ; simp [Real.cos_add_two_pi]
  have := (pf_decay_aux k _ hF hper B hB j hj).1
  have hj0 : j ≠ 0 := by omega
  unfold coef
  rw [if_neg hj0, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  calc 1 / Real.pi * |∫ θ in (0 : ℝ)..2 * Real.pi, φ (K * Real.cos θ) * Real.cos (j * θ)|
      ≤ 1 / Real.pi * (2 * Real.pi * B / (j:ℝ)^k) := mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 * B / (j:ℝ)^k := by field_simp



theorem coef_zero_bound (K : ℝ) (hK : 0 < K) (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    |coef K φ 0| ≤ cNorm 0 φ (-K) K := by
  have hc : Continuous φ := hφ.continuous
  have hbdd : BddAbove ((fun x => |φ x|) '' Set.Icc (-K) K) :=
    (isCompact_Icc.image (by fun_prop)).bddAbove
  have hM : ∀ x ∈ Set.Icc (-K) K, |φ x| ≤ cNorm 0 φ (-K) K := by
    intro x hx
    simp only [cNorm, zero_add, Finset.range_one, Finset.sum_singleton, iteratedDeriv_zero, supOn]
    exact le_csSup hbdd ⟨x, hx, rfl⟩
  have hM0 : 0 ≤ cNorm 0 φ (-K) K :=
    (abs_nonneg _).trans (hM 0 ⟨by linarith, by linarith⟩)
  have two : (0:ℝ) < 2 * Real.pi := by positivity
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (f := fun θ => φ (K * Real.cos θ) * Real.cos ((0:ℕ) * θ)) (C := cNorm 0 φ (-K) K) (fun x _ => by
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |φ (K * Real.cos x)| ≤ cNorm 0 φ (-K) K := hM _ ⟨by
          nlinarith [Real.neg_one_le_cos x], by nlinarith [Real.cos_le_one x]⟩
      calc |φ (K * Real.cos x)| * |Real.cos (((0:ℕ):ℝ) * x)| ≤ cNorm 0 φ (-K) K * 1 :=
            mul_le_mul h1 (Real.abs_cos_le_one _) (abs_nonneg _) hM0
        _ = _ := mul_one _)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos two] at this
  unfold coef
  rw [if_pos rfl, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
  calc 1 / (2 * Real.pi) * |∫ θ in (0 : ℝ)..2 * Real.pi, φ (K * Real.cos θ) * Real.cos (((0:ℕ):ℝ) * θ)|
      ≤ 1 / (2 * Real.pi) * (cNorm 0 φ (-K) K * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by field_simp

theorem coef_add (K : ℝ) (φ ψ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (j : ℕ) : coef K (φ + ψ) j = coef K φ j + coef K ψ j := by
  have h1 : Continuous φ := hφ.continuous
  have h2 : Continuous ψ := hψ.continuous
  unfold coef
  rw [← mul_add, ← intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
  congr 2; ext θ; simp [add_mul]

theorem coef_smul (K : ℝ) (s : ℝ) (φ : ℝ → ℝ) (j : ℕ) : coef K (s • φ) j = s * coef K φ j := by
  unfold coef
  rw [show (∫ θ in (0 : ℝ)..2 * Real.pi, (s • φ) (K * Real.cos θ) * Real.cos (j * θ))
    = s * ∫ θ in (0 : ℝ)..2 * Real.pi, φ (K * Real.cos θ) * Real.cos (j * θ) from by
      rw [← intervalIntegral.integral_const_mul]; congr 1; ext θ; simp [mul_assoc]]
  ring



lemma pf_int_cos (c : ℤ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos ((c : ℝ) * θ) = if c = 0 then 2 * Real.pi else 0 := by
  by_cases hc : c = 0
  · subst hc; simp
  · have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    rw [if_neg hc, intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc']
    simp only [integral_cos, mul_zero, Real.sin_zero, smul_eq_mul]
    have : Real.sin ((c : ℝ) * (2 * Real.pi)) = 0 := by
      have := Real.sin_int_mul_pi (2 * c)
      rw [show (((2 * c : ℤ)) : ℝ) * Real.pi = c * (2 * Real.pi) by push_cast; ring] at this
      exact this
    rw [this]; simp

lemma pf_orth (i j : ℕ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos (i * θ) * Real.cos (j * θ)
      = if i = j then (if j = 0 then 2 * Real.pi else Real.pi) else 0 := by
  have e : ∀ θ : ℝ, Real.cos (i * θ) * Real.cos (j * θ)
      = (1/2) * (Real.cos ((((i:ℤ) - j : ℤ) : ℝ) * θ) + Real.cos ((((i:ℤ) + j : ℤ) : ℝ) * θ)) := by
    intro θ
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    pf_int_cos, pf_int_cos]
  by_cases hij : i = j
  · subst hij
    by_cases h0 : i = 0
    · subst h0; simp; ring
    · have : ((i:ℤ) + i) ≠ 0 := by omega
      simp [h0, this]
  · have h1 : ((i:ℤ) - j) ≠ 0 := by omega
    by_cases h2 : ((i:ℤ) + j) = 0
    · have : i = 0 := by omega
      have : j = 0 := by omega
      exact absurd (by omega) hij
    · simp [hij, h1, h2]

lemma pf_cheb_degree (K : ℝ) (hK : 0 < K) (j : ℕ) :
    (cheb K j).natDegree = j ∧ (cheb K j).coeff j ≠ 0 := by
  have hq : (Polynomial.C K⁻¹ * X : ℝ[X]).natDegree = 1 := by
    rw [natDegree_C_mul_X _ (inv_ne_zero hK.ne')]
  have hnd : (cheb K j).natDegree = j := by
    unfold cheb
    rw [natDegree_comp, hq]; simp
  refine ⟨hnd, ?_⟩
  have : (cheb K j).leadingCoeff ≠ 0 := by
    unfold cheb
    rw [leadingCoeff_comp (by rw [hq]; norm_num)]
    have : (Polynomial.C K⁻¹ * X : ℝ[X]).leadingCoeff = K⁻¹ := by
      rw [leadingCoeff_C_mul_X]
    rw [this]
    have h2 : (Chebyshev.T ℝ (j:ℤ)).leadingCoeff ≠ 0 := by
      rw [Chebyshev.leadingCoeff_T]; positivity
    exact mul_ne_zero h2 (pow_ne_zero _ (inv_ne_zero hK.ne'))
  rwa [leadingCoeff, hnd] at this

lemma pf_expand (K : ℝ) (hK : 0 < K) : ∀ n : ℕ, ∀ h : ℝ[X], h.natDegree ≤ n →
    ∃ b : ℕ → ℝ, (∀ j, n < j → b j = 0) ∧
      h = ∑ j ∈ Finset.range (n + 1), Polynomial.C (b j) * cheb K j := by
  intro n
  induction n with
  | zero =>
    intro h hh
    refine ⟨fun j => if j = 0 then h.coeff 0 else 0, fun j hj => by simp [Nat.pos_iff_ne_zero.mp hj], ?_⟩
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, if_true]
    have : cheb K 0 = 1 := by simp [cheb]
    rw [this, mul_one]
    exact eq_C_of_natDegree_le_zero hh
  | succ n ih =>
    intro h hh
    obtain ⟨hd, hc⟩ := pf_cheb_degree K hK (n+1)
    set a := h.coeff (n+1) / (cheb K (n+1)).coeff (n+1) with ha
    have hdeg : (h - Polynomial.C a * cheb K (n+1)).natDegree ≤ n := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rcases Nat.lt_or_ge (n+1) N with h1 | h1
      · rw [coeff_eq_zero_of_natDegree_lt]
        calc (h - Polynomial.C a * cheb K (n+1)).natDegree
            ≤ n + 1 := (natDegree_sub_le _ _).trans
              (max_le hh ((natDegree_C_mul_le _ _).trans hd.le))
          _ < N := h1
      · have : N = n + 1 := by omega
        subst this
        rw [coeff_sub, coeff_C_mul, ha]
        field_simp
        ring
    obtain ⟨b', hb'0, hb'⟩ := ih _ hdeg
    refine ⟨fun j => if j = n + 1 then a else b' j, fun j hj => ?_, ?_⟩
    · have : j ≠ n + 1 := by omega
      simp only [this, if_false]; exact hb'0 j (by omega)
    · rw [Finset.sum_range_succ]
      have : ∑ j ∈ Finset.range (n + 1), Polynomial.C (if j = n + 1 then a else b' j) * cheb K j
          = ∑ j ∈ Finset.range (n + 1), Polynomial.C (b' j) * cheb K j := by
        apply Finset.sum_congr rfl
        intro j hj
        have : j ≠ n + 1 := by have := Finset.mem_range.mp hj; omega
        simp [this]
      rw [this, ← hb']
      simp

lemma pf_eval_cheb (K : ℝ) (hK : 0 < K) (i : ℕ) (θ : ℝ) :
    (cheb K i).eval (K * Real.cos θ) = Real.cos (i * θ) := by
  unfold cheb
  rw [eval_comp]
  simp only [eval_mul, eval_C, eval_X]
  rw [← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul]
  have := Chebyshev.T_real_cos θ (i : ℤ)
  simpa using this

theorem coef_poly (K : ℝ) (hK : 0 < K) (h : ℝ[X]) :
    ∃ b : ℕ → ℝ, (∀ j, h.natDegree < j → b j = 0) ∧
      h = ∑ j ∈ Finset.range (h.natDegree + 1), Polynomial.C (b j) * cheb K j ∧
      ∀ j, coef K (fun x => h.eval x) j = b j := by
  obtain ⟨b, hb0, hb⟩ := pf_expand K hK h.natDegree h le_rfl
  refine ⟨b, hb0, hb, fun j => ?_⟩
  set n := h.natDegree
  have hev : ∀ θ : ℝ, h.eval (K * Real.cos θ) = ∑ i ∈ Finset.range (n + 1), b i * Real.cos (i * θ) := by
    intro θ
    conv_lhs => rw [hb]
    rw [eval_finset_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [eval_mul, eval_C, pf_eval_cheb K hK]
  have hint : ∫ θ in (0 : ℝ)..2 * Real.pi, h.eval (K * Real.cos θ) * Real.cos (j * θ)
      = ∑ i ∈ Finset.range (n + 1), b i * (if i = j then (if j = 0 then 2 * Real.pi else Real.pi) else 0) := by
    simp_rw [hev, Finset.sum_mul]
    rw [intervalIntegral.integral_finset_sum (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (fun θ : ℝ => b i * Real.cos (i * θ) * Real.cos (j * θ))
        = fun θ => b i * (Real.cos (i * θ) * Real.cos (j * θ)) from by funext θ; ring,
      intervalIntegral.integral_const_mul, pf_orth]
  unfold coef
  rw [hint]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
  by_cases hj : j < n + 1
  · rw [if_pos hj]
    by_cases h0 : j = 0
    · subst h0; simp; field_simp
    · simp only [h0, if_false]; field_simp
  · rw [if_neg hj, hb0 j (by omega)]

end StrongConvS4.PartF

end
end

section
section
open Polynomial

namespace StrongConvS4.PartG
open StrongConvS4 StrongConv

lemma supOn_nonneg' (f : ℝ → ℝ) (a b : ℝ) : 0 ≤ supOn f a b :=
  Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact abs_nonneg _)

lemma le_supOn' {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Set.Icc a b)) {x : ℝ}
    (hx : x ∈ Set.Icc a b) : |f x| ≤ supOn f a b :=
  le_csSup (isCompact_Icc.bddAbove_image (continuous_abs.comp_continuousOn hf)) ⟨x, hx, rfl⟩

lemma supOn_le' {f : ℝ → ℝ} {a b ε : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Set.Icc a b, |f x| ≤ ε) :
    supOn f a b ≤ ε :=
  csSup_le ⟨_, ⟨a, ⟨le_rfl, hab⟩, rfl⟩⟩ (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

lemma cNorm_le' {m : ℕ} {f : ℝ → ℝ} {a b ε : ℝ} (hab : a ≤ b)
    (h : ∀ j ≤ m, ∀ x ∈ Set.Icc a b, |iteratedDeriv j f x| ≤ ε) :
    cNorm m f a b ≤ (m + 1) * ε := by
  unfold cNorm
  calc ∑ j ∈ Finset.range (m + 1), supOn (iteratedDeriv j f) a b
      ≤ ∑ j ∈ Finset.range (m + 1), ε :=
        Finset.sum_le_sum fun j hj =>
          supOn_le' hab (h j (by simpa [Nat.lt_succ_iff] using hj))
    _ = (m + 1) * ε := by simp

/-- The algebra generated by `sin` and `cos`. -/
def A : Subalgebra ℝ (ℝ → ℝ) := Algebra.adjoin ℝ {Real.sin, Real.cos}

lemma sin_mem : Real.sin ∈ A := Algebra.subset_adjoin (by simp)
lemma cos_mem : Real.cos ∈ A := Algebra.subset_adjoin (by simp)

lemma A_prop {p : ℝ → ℝ} (hp : p ∈ A) :
    ContDiff ℝ (⊤ : ℕ∞) p ∧ deriv p ∈ A ∧ ∃ B, ∀ θ, |p θ| ≤ B := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · refine ⟨Real.contDiff_sin, ?_, 1, Real.abs_sin_le_one⟩
      rw [Real.deriv_sin]; exact cos_mem
    · refine ⟨Real.contDiff_cos, ?_, 1, Real.abs_cos_le_one⟩
      rw [Real.deriv_cos']; exact A.neg_mem sin_mem
  | algebraMap r =>
    refine ⟨contDiff_const, ?_, |r|, fun θ => le_rfl⟩
    have : deriv (algebraMap ℝ (ℝ → ℝ) r) = 0 := by
      have : algebraMap ℝ (ℝ → ℝ) r = fun _ => r := rfl
      rw [this]; ext; simp
    rw [this]; exact A.zero_mem
  | add x y hx hy ihx ihy =>
    obtain ⟨c1, d1, B1, b1⟩ := ihx
    obtain ⟨c2, d2, B2, b2⟩ := ihy
    refine ⟨c1.add c2, ?_, B1 + B2, fun θ => (abs_add_le _ _).trans (add_le_add (b1 θ) (b2 θ))⟩
    have : deriv (x + y) = deriv x + deriv y := by
      ext t
      exact deriv_add (c1.differentiable (by simp) t) (c2.differentiable (by simp) t)
    rw [this]; exact A.add_mem d1 d2
  | mul x y hx hy ihx ihy =>
    obtain ⟨c1, d1, B1, b1⟩ := ihx
    obtain ⟨c2, d2, B2, b2⟩ := ihy
    refine ⟨c1.mul c2, ?_, B1 * B2 + 0, ?_⟩
    · have : deriv (x * y) = deriv x * y + x * deriv y := by
        ext t
        exact deriv_mul (c1.differentiable (by simp) t) (c2.differentiable (by simp) t)
      rw [this]; exact A.add_mem (A.mul_mem d1 hy) (A.mul_mem hx d2)
    · intro θ
      have h0 : 0 ≤ B1 := (abs_nonneg _).trans (b1 θ)
      simp only [Pi.mul_apply, abs_mul, add_zero]
      exact mul_le_mul (b1 θ) (b2 θ) (abs_nonneg _) h0

lemma rep (K : ℝ) (k : ℕ) :
    ∃ p : ℕ → ℝ → ℝ, (∀ i, p i ∈ A) ∧ ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → ∀ θ,
      iteratedDeriv k (fun θ => φ (K * Real.cos θ)) θ =
        ∑ i ∈ Finset.range (k + 1), p i θ * iteratedDeriv i φ (K * Real.cos θ) := by
  induction k with
  | zero =>
    refine ⟨fun _ => 1, fun _ => A.one_mem, fun φ _ θ => ?_⟩
    simp
  | succ k ih =>
    obtain ⟨p, hpA, H⟩ := ih
    refine ⟨fun i => (if i ≤ k then deriv (p i) else 0) +
      (if i = 0 then 0 else p (i - 1) * ((-K) • Real.sin)), ?_, ?_⟩
    · intro i
      refine A.add_mem ?_ ?_
      · split_ifs
        · exact (A_prop (hpA i)).2.1
        · exact A.zero_mem
      · split_ifs
        · exact A.zero_mem
        · exact A.mul_mem (hpA _) (A.smul_mem sin_mem _)
    · intro φ hφ θ
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv k (fun θ => φ (K * Real.cos θ)) = fun θ =>
          ∑ i ∈ Finset.range (k + 1), p i θ * iteratedDeriv i φ (K * Real.cos θ) :=
        funext (H φ hφ)
      rw [hfun]
      have hd : ∀ i ∈ Finset.range (k + 1), HasDerivAt
          (fun t => p i t * iteratedDeriv i φ (K * Real.cos t))
          (deriv (p i) θ * iteratedDeriv i φ (K * Real.cos θ) +
            p i θ * (iteratedDeriv (i + 1) φ (K * Real.cos θ) * (K * -Real.sin θ))) θ := by
        intro i _
        have h1 : HasDerivAt (p i) (deriv (p i) θ) θ :=
          ((A_prop (hpA i)).1.differentiable (by simp) θ).hasDerivAt
        have h2 : HasDerivAt (iteratedDeriv i φ) (iteratedDeriv (i + 1) φ (K * Real.cos θ))
            (K * Real.cos θ) := by
          rw [iteratedDeriv_succ]
          exact ((hφ.differentiable_iteratedDeriv i (by exact_mod_cast ENat.natCast_lt_top i)) _).hasDerivAt
        have h3 : HasDerivAt (fun t => K * Real.cos t) (K * -Real.sin θ) θ :=
          (Real.hasDerivAt_cos θ).const_mul K
        have h4 : HasDerivAt (fun t => iteratedDeriv i φ (K * Real.cos t))
            (iteratedDeriv (i + 1) φ (K * Real.cos θ) * (K * -Real.sin θ)) θ := HasDerivAt.comp (h := fun t => K * Real.cos t) θ h2 h3
        exact h1.mul h4
      rw [(HasDerivAt.fun_sum hd).deriv]
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_range_succ (fun x => (if x ≤ k then deriv (p x) else 0) θ *
        iteratedDeriv x φ (K * Real.cos θ))]
      rw [Finset.sum_range_succ' (fun x => (if x = 0 then 0 else p (x - 1) * ((-K) • Real.sin)) θ *
        iteratedDeriv x φ (K * Real.cos θ))]
      have e1 : ∑ x ∈ Finset.range (k + 1), (if x ≤ k then deriv (p x) else 0) θ *
          iteratedDeriv x φ (K * Real.cos θ) =
          ∑ x ∈ Finset.range (k + 1), deriv (p x) θ * iteratedDeriv x φ (K * Real.cos θ) :=
        Finset.sum_congr rfl (fun x hx => by simp [Nat.lt_succ_iff.1 (Finset.mem_range.1 hx)])
      rw [e1]
      simp [mul_comm, mul_left_comm]

theorem comp_cos_bound (K : ℝ) (hK : 0 < K) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → ∀ θ : ℝ,
      |iteratedDeriv k (fun θ => φ (K * Real.cos θ)) θ| ≤ C * cNorm k φ (-K) K := by
  obtain ⟨p, hpA, H⟩ := rep K k
  have hB : ∀ i, ∃ B, 0 ≤ B ∧ ∀ θ, |p i θ| ≤ B := fun i => by
    obtain ⟨B, hB⟩ := (A_prop (hpA i)).2.2
    exact ⟨B, (abs_nonneg _).trans (hB 0), hB⟩
  choose B hB0 hB using hB
  refine ⟨∑ i ∈ Finset.range (k + 1), B i, Finset.sum_nonneg fun i _ => hB0 i,
    fun φ hφ θ => ?_⟩
  rw [H φ hφ θ]
  have hmem : K * Real.cos θ ∈ Set.Icc (-K) K := by
    constructor <;> nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  calc |∑ i ∈ Finset.range (k + 1), p i θ * iteratedDeriv i φ (K * Real.cos θ)|
      ≤ ∑ i ∈ Finset.range (k + 1), |p i θ * iteratedDeriv i φ (K * Real.cos θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), B i * supOn (iteratedDeriv i φ) (-K) K :=
        Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul (hB i θ)
            (le_supOn' (hφ.continuous_iteratedDeriv i (by exact_mod_cast le_top)).continuousOn hmem)
            (abs_nonneg _) (hB0 i)
    _ ≤ ∑ i ∈ Finset.range (k + 1), B i * cNorm k φ (-K) K :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun j => supOn (iteratedDeriv j φ) (-K) K)
            (fun j _ => supOn_nonneg' _ _ _) hi) (hB0 i)
    _ = _ := by rw [Finset.sum_mul]

lemma exists_antideriv (P1 : ℝ[X]) : ∃ Q : ℝ[X], derivative Q = P1 := by
  induction P1 using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by simp [ha, hb]⟩
  | monomial n a =>
    refine ⟨monomial (n + 1) (a / (n + 1)), ?_⟩
    rw [derivative_monomial]
    simp only [Nat.add_sub_cancel]
    congr 1
    push_cast
    field_simp

lemma poly_dense (K0 : ℝ) (hK0 : 0 ≤ K0) : ∀ (M : ℕ) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
    ∀ ε > 0, ∃ P : ℝ[X], ∀ j ≤ M, ∀ x ∈ Set.Icc (-K0) K0,
      |iteratedDeriv j φ x - iteratedDeriv j (fun x => P.eval x) x| ≤ ε := by
  intro M
  induction M with
  | zero =>
    intro φ hφ ε hε
    obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-K0) K0 φ hφ.continuous.continuousOn ε hε
    refine ⟨P, fun j hj x hx => ?_⟩
    obtain rfl : j = 0 := by omega
    simp only [iteratedDeriv_zero]
    rw [abs_sub_comm]
    exact (hP x hx).le
  | succ M ih =>
    intro φ hφ ε hε
    have hφ' : ContDiff ℝ (⊤ : ℕ∞) (deriv φ) := (contDiff_infty_iff_deriv.1 hφ).2
    have hε' : 0 < ε / (2 * K0 + 1) := by positivity
    obtain ⟨P1, hP1⟩ := ih (deriv φ) hφ' _ hε'
    obtain ⟨Q, hQ⟩ := exists_antideriv P1
    set P : ℝ[X] := Q + Polynomial.C (φ (-K0) - Q.eval (-K0)) with hPdef
    have hdP : derivative P = P1 := by simp [hPdef, hQ]
    have hdPf : deriv (fun x => P.eval x) = fun x => P1.eval x := by
      funext x; rw [Polynomial.deriv, hdP]
    refine ⟨P, fun j hj x hx => ?_⟩
    rcases j with _ | j
    · simp only [iteratedDeriv_zero]
      have h0 := hP1 0 (Nat.zero_le _)
      simp only [iteratedDeriv_zero] at h0
      have hdiff : ∀ y ∈ Set.Icc (-K0) K0, DifferentiableAt ℝ (fun x => φ x - P.eval x) y :=
        fun y _ => (hφ.differentiable (by simp) y).sub (P.differentiableAt)
      have hder : ∀ y ∈ Set.Icc (-K0) K0, ‖deriv (fun x => φ x - P.eval x) y‖ ≤ ε / (2 * K0 + 1) := by
        intro y hy
        have : deriv (fun x => φ x - P.eval x) y = deriv φ y - P1.eval y := by
          have hh := ((hφ.differentiable (by simp) y).hasDerivAt.sub
            (Polynomial.hasDerivAt P y)).deriv
          rw [hdP] at hh
          exact hh
        rw [this, Real.norm_eq_abs]
        exact h0 y hy
      have hm := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hder (convex_Icc (-K0) K0)
        (x := -K0) (y := x) ⟨le_rfl, by linarith [hx.1, hx.2]⟩ hx
      have h00 : φ (-K0) - P.eval (-K0) = 0 := by
        simp [hPdef]
      rw [h00, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at hm
      have : |x - -K0| ≤ 2 * K0 := by
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      calc |φ x - P.eval x| ≤ ε / (2 * K0 + 1) * |x - -K0| := hm
        _ ≤ ε / (2 * K0 + 1) * (2 * K0) := mul_le_mul_of_nonneg_left this hε'.le
        _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
    · rw [iteratedDeriv_succ', iteratedDeriv_succ', hdPf]
      have := hP1 j (by omega) x hx
      refine this.trans ?_
      exact div_le_self hε.le (by linarith)

lemma cNorm_sub_poly {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (P : ℝ[X]) {ε K K0 : ℝ}
    {m M : ℕ} (hK : 0 < K) (hKK : K ≤ K0) (hmM : m ≤ M)
    (hP : ∀ j ≤ M, ∀ x ∈ Set.Icc (-K0) K0,
      |iteratedDeriv j φ x - iteratedDeriv j (fun x => P.eval x) x| ≤ ε) :
    cNorm m (φ - fun x => P.eval x) (-K) K ≤ (m + 1) * ε := by
  apply cNorm_le' (by linarith)
  intro j hj x hx
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun x => P.eval x) := (polyFun P).2
  rw [iteratedDeriv_sub (hφ.contDiffAt.of_le (by exact_mod_cast le_top))
    (hp.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact hP j (hj.trans hmM) x ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem uniq_cs (μ μ' : smoothFun →ₗ[ℝ] ℝ) (h : IsCSDistribution μ) (h' : IsCSDistribution μ')
    (he : ∀ h : ℝ[X], μ (polyFun h) = μ' (polyFun h)) : μ = μ' := by
  obtain ⟨c, K, m, hc, hK, hμ⟩ := h
  obtain ⟨c', K', m', hc', hK', hμ'⟩ := h'
  apply LinearMap.ext
  rintro ⟨φ, hφ⟩
  have hA : 0 < c * (m + 1) + c' * (m' + 1) := by positivity
  suffices hz : ∀ ε > 0, |μ ⟨φ, hφ⟩ - μ' ⟨φ, hφ⟩| ≤ ε * (c * (m + 1) + c' * (m' + 1)) by
    by_contra hne
    have hd : 0 < |μ ⟨φ, hφ⟩ - μ' ⟨φ, hφ⟩| := abs_pos.2 (sub_ne_zero.2 hne)
    have := hz (|μ ⟨φ, hφ⟩ - μ' ⟨φ, hφ⟩| / (2 * (c * (m + 1) + c' * (m' + 1)))) (by positivity)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
    nlinarith
  intro ε hε
  obtain ⟨P, hP⟩ := poly_dense (max K K') (le_trans hK.le (le_max_left _ _)) (max m m') φ hφ ε hε
  have key : μ ⟨φ, hφ⟩ - μ' ⟨φ, hφ⟩ =
      μ (⟨φ, hφ⟩ - polyFun P) - μ' (⟨φ, hφ⟩ - polyFun P) := by
    rw [map_sub, map_sub, he P]; ring
  rw [key]
  have b1 : |μ (⟨φ, hφ⟩ - polyFun P)| ≤ c * ((m + 1) * ε) :=
    (hμ _).trans (mul_le_mul_of_nonneg_left
      (cNorm_sub_poly hφ P hK (le_max_left _ _) (le_max_left _ _) hP) hc.le)
  have b2 : |μ' (⟨φ, hφ⟩ - polyFun P)| ≤ c' * ((m' + 1) * ε) :=
    (hμ' _).trans (mul_le_mul_of_nonneg_left
      (cNorm_sub_poly hφ P hK' (le_max_right _ _) (le_max_right _ _) hP) hc'.le)
  calc _ ≤ |μ (⟨φ, hφ⟩ - polyFun P)| + |μ' (⟨φ, hφ⟩ - polyFun P)| := abs_sub _ _
    _ ≤ _ := by nlinarith

lemma cNorm_zero' (F : ℝ → ℝ) (a b : ℝ) : cNorm 0 F a b = supOn F a b := by
  simp [cNorm]

lemma poly_cd (g : ℝ[X]) : ContDiff ℝ (⊤ : ℕ∞) (fun x => g.eval x) := (polyFun g).2

lemma poly_cont (g : ℝ[X]) (i : ℕ) : Continuous (iteratedDeriv i (fun x => g.eval x)) :=
  (poly_cd g).continuous_iteratedDeriv i (by exact_mod_cast le_top)

lemma markov_pt (q : ℕ) (h : ℝ[X]) (hh : h.natDegree ≤ q) {K : ℝ} (hK : 0 < K) (i : ℕ) :
    supOn (iteratedDeriv i (fun x => h.eval x)) (-K) K ≤
      ((q : ℝ) ^ 2 / K) ^ i * supOn (fun x => h.eval x) (-K) K := by
  set g : ℝ[X] := h.comp (X - C K) with hg
  have hgd : g.natDegree ≤ q := by
    rw [hg, natDegree_comp, natDegree_X_sub_C, mul_one]; exact hh
  have T := cNorm_iteratedDeriv_le q i g hgd (2 * K) (by linarith)
  rw [cNorm_zero', cNorm_zero'] at T
  have hG : (fun y => g.eval y) = fun z => (fun x => h.eval x) (z - K) := by
    funext z; simp [hg, eval_comp]
  have hGi : iteratedDeriv i (fun y => g.eval y) = fun t => iteratedDeriv i (fun x => h.eval x) (t - K) := by
    rw [hG]; exact iteratedDeriv_comp_sub_const i (fun x => h.eval x) K
  have hS0 := supOn_nonneg' (fun x => h.eval x) (-K) K
  have hfc : ContinuousOn (fun x => h.eval x) (Set.Icc (-K) K) := (poly_cd h).continuous.continuousOn
  have h1 : supOn (iteratedDeriv i (fun x => h.eval x)) (-K) K ≤
      supOn (iteratedDeriv i (fun y => g.eval y)) 0 (2 * K) := by
    apply supOn_le' (by linarith)
    intro x hx
    have e : |iteratedDeriv i (fun x => h.eval x) x| =
        |iteratedDeriv i (fun y => g.eval y) (x + K)| := by rw [hGi]; simp
    rw [e]
    exact le_supOn' (poly_cont g i).continuousOn (x := x + K) (a := 0) (b := 2 * K)
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h2 : supOn (fun y => g.eval y) 0 (2 * K) ≤ supOn (fun x => h.eval x) (-K) K := by
    apply supOn_le' (by linarith)
    intro y hy
    have e : g.eval y = h.eval (y - K) := by simp [hg, eval_comp]
    rw [e]
    exact le_supOn' hfc (x := y - K) ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hfac : 1 / (((2 * i - 1).doubleFactorial : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast Nat.doubleFactorial_pos _)]
    exact_mod_cast Nat.doubleFactorial_pos _
  have e : (2 * (q : ℝ) ^ 2 / (2 * K)) = (q : ℝ) ^ 2 / K := by field_simp
  rw [e] at T
  have hp : 0 ≤ ((q : ℝ) ^ 2 / K) ^ i := by positivity
  calc _ ≤ _ := h1
    _ ≤ _ := T
    _ ≤ 1 * ((q : ℝ) ^ 2 / K) ^ i * supOn (fun y => g.eval y) 0 (2 * K) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hfac hp
        · exact supOn_nonneg' _ _ _
    _ ≤ 1 * ((q : ℝ) ^ 2 / K) ^ i * supOn (fun x => h.eval x) (-K) K :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

theorem one_of_cs (μ : smoothFun →ₗ[ℝ] ℝ) (hμ : IsCSDistribution μ) :
    ∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
      |μ (polyFun h)| ≤ c * (q : ℝ) ^ m * cNorm 0 (fun x => h.eval x) (-K) K := by
  obtain ⟨c, K, m, hc, hK, hμ⟩ := hμ
  set M : ℝ := max 1 K⁻¹ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  refine ⟨c * (m + 1) * M ^ m, ((2 * m : ℕ) : ℝ), K, by positivity, by positivity, hK.le, ?_⟩
  intro q hq h hh
  rw [Real.rpow_natCast, cNorm_zero']
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hS0 := supOn_nonneg' (fun x => h.eval x) (-K) K
  have step : cNorm m (fun x => h.eval x) (-K) K ≤ (m + 1) * ((q : ℝ) ^ (2 * m) * M ^ m) *
      supOn (fun x => h.eval x) (-K) K := by
    unfold cNorm
    have : ∀ i ∈ Finset.range (m + 1), supOn (iteratedDeriv i (fun x => h.eval x)) (-K) K ≤
        ((q : ℝ) ^ (2 * m) * M ^ m) * supOn (fun x => h.eval x) (-K) K := by
      intro i hi
      have hi' : i ≤ m := by simpa [Nat.lt_succ_iff] using hi
      refine (markov_pt q h hh hK i).trans (mul_le_mul_of_nonneg_right ?_ hS0)
      rw [div_eq_mul_inv, mul_pow, ← pow_mul]
      have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ hq1
      refine mul_le_mul (pow_le_pow_right₀ hq1 (by omega)) ?_ (by positivity) (by positivity)
      exact (pow_le_pow_left₀ (inv_nonneg.2 hK.le) (le_max_right _ _) i).trans
        (pow_le_pow_right₀ hM1 hi')
    calc _ ≤ ∑ i ∈ Finset.range (m + 1), ((q : ℝ) ^ (2 * m) * M ^ m) * supOn (fun x => h.eval x) (-K) K :=
          Finset.sum_le_sum this
      _ = _ := by simp; ring
  calc |μ (polyFun h)| ≤ c * cNorm m (fun x => h.eval x) (-K) K := hμ (polyFun h)
    _ ≤ c * ((m + 1) * ((q : ℝ) ^ (2 * m) * M ^ m) * supOn (fun x => h.eval x) (-K) K) :=
        mul_le_mul_of_nonneg_left step hc.le
    _ = _ := by ring

end StrongConvS4.PartG

end
end

section
section
open Polynomial

namespace StrongConvS4
open StrongConv

lemma cN_nonneg' (k : ℕ) (φ : ℝ → ℝ) (a b : ℝ) : 0 ≤ cNorm k φ a b :=
  Finset.sum_nonneg fun j _ => Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact abs_nonneg _)

lemma cN_mono' (k : ℕ) (φ : ℝ → ℝ) (a b : ℝ) : cNorm 0 φ a b ≤ cNorm k φ a b := by
  unfold cNorm
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj; simp at hj ⊢; omega
  · intros; exact Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact abs_nonneg _)

lemma cN0_le {F : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Set.Icc a b, |F x| ≤ B) :
    cNorm 0 F a b ≤ B := by
  simp only [cNorm, supOn, zero_add, Finset.sum_range_one, iteratedDeriv_zero]
  apply csSup_le
  · exact ⟨_, Set.mem_image_of_mem _ (Set.left_mem_Icc.2 hab)⟩
  · rintro _ ⟨x, hx, rfl⟩; exact h x hx

theorem ext_exists (ν : ℝ[X] →ₗ[ℝ] ℝ) (c m K : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m) (hK : 0 < K)
    (h2 : ∀ j : ℕ, 1 ≤ j → |ν (cheb K j)| ≤ c * (j : ℝ) ^ m) :
    ∃ μ : smoothFun →ₗ[ℝ] ℝ, IsCSDistribution μ ∧ ∀ h : ℝ[X], μ (polyFun h) = ν h := by
  set m' : ℕ := ⌈m⌉₊ with hm'
  set k : ℕ := m' + 2 with hk
  obtain ⟨C, hC0, hC⟩ := PartG.comp_cos_bound K hK k
  set Z : ℝ := ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ 2 with hZ
  have hZs : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (one_lt_two))
    simpa using this
  have hZ0 : 0 ≤ Z := tsum_nonneg fun j => by positivity
  -- term bounds
  have hterm : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → ∀ j : ℕ,
      |coef K φ (j + 1) * ν (cheb K (j + 1))| ≤
        2 * c * C * cNorm k φ (-K) K * (1 / ((j : ℝ) + 1) ^ 2) := by
    intro φ hφ j
    have hd := PartF.coef_decay K φ hφ k (C * cNorm k φ (-K) K) (hC φ hφ) (j + 1) (by omega)
    have hν := h2 (j + 1) (by omega)
    have hj1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
    have hpow : ((j + 1 : ℕ) : ℝ) ^ m ≤ ((j + 1 : ℕ) : ℝ) ^ (m' : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hj1 (Nat.le_ceil m)
    rw [Real.rpow_natCast] at hpow
    have hjp : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by linarith
    rw [abs_mul]
    calc |coef K φ (j + 1)| * |ν (cheb K (j + 1))|
        ≤ (2 * (C * cNorm k φ (-K) K) / ((j + 1 : ℕ) : ℝ) ^ k) * (c * ((j + 1 : ℕ) : ℝ) ^ m') := by
          apply mul_le_mul hd (hν.trans (mul_le_mul_of_nonneg_left hpow hc)) (abs_nonneg _)
          exact div_nonneg (mul_nonneg (by norm_num) (mul_nonneg hC0 (cN_nonneg' _ _ _ _))) (by positivity)
      _ = 2 * c * C * cNorm k φ (-K) K * (1 / ((j : ℝ) + 1) ^ 2) := by
          rw [hk, pow_add]
          push_cast
          field_simp
  have hsumm : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      Summable (fun j : ℕ => coef K φ j * ν (cheb K j)) := by
    intro φ hφ
    rw [← summable_nat_add_iff 1]
    refine Summable.of_norm_bounded (hZs.mul_left (2 * c * C * cNorm k φ (-K) K)) fun j => ?_
    rw [Real.norm_eq_abs]; exact hterm φ hφ j
  have hbound : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      |∑' j, coef K φ j * ν (cheb K j)| ≤
        (|ν (cheb K 0)| + 2 * c * C * Z) * cNorm k φ (-K) K := by
    intro φ hφ
    have hs := hsumm φ hφ
    rw [hs.tsum_eq_zero_add]
    have hs1 : Summable (fun j : ℕ => coef K φ (j + 1) * ν (cheb K (j + 1))) :=
      (summable_nat_add_iff 1).2 hs
    have h1 : |∑' j : ℕ, coef K φ (j + 1) * ν (cheb K (j + 1))| ≤
        2 * c * C * cNorm k φ (-K) K * Z := by
      have := tsum_of_norm_bounded (hZs.mul_left (2 * c * C * cNorm k φ (-K) K)).hasSum
        (fun j => by rw [Real.norm_eq_abs]; exact hterm φ hφ j)
      rw [tsum_mul_left] at this
      simpa [hZ] using this
    have h0 : |coef K φ 0 * ν (cheb K 0)| ≤ |ν (cheb K 0)| * cNorm k φ (-K) K := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left
        ((PartF.coef_zero_bound K hK φ hφ).trans (cN_mono' k φ (-K) K)) (abs_nonneg _)
    calc _ ≤ |coef K φ 0 * ν (cheb K 0)| + |∑' j : ℕ, coef K φ (j + 1) * ν (cheb K (j + 1))| :=
          abs_add_le _ _
      _ ≤ _ := by nlinarith [cN_nonneg' k φ (-K) K]
  let μ : smoothFun →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∑' j, coef K f.1 j * ν (cheb K j)
      map_add' := by
        intro f g
        have hf : ContDiff ℝ (⊤ : ℕ∞) f.1 := f.2
        have hg : ContDiff ℝ (⊤ : ℕ∞) g.1 := g.2
        simp only [Submodule.coe_add]
        rw [← Summable.tsum_add (hsumm _ hf) (hsumm _ hg)]
        congr 1; ext j
        rw [PartF.coef_add K _ _ hf hg j, add_mul]
      map_smul' := by
        intro s f
        simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
        rw [← tsum_mul_left]
        congr 1; ext j
        rw [PartF.coef_smul]; ring }
  refine ⟨μ, ⟨(|ν (cheb K 0)| + 2 * c * C * Z) + 1, K, k, by positivity, hK, fun f => ?_⟩, ?_⟩
  · have := hbound f.1 f.2
    have hn := cN_nonneg' k f.1 (-K) K
    show |∑' j, coef K f.1 j * ν (cheb K j)| ≤ _
    nlinarith
  · intro h
    obtain ⟨b, hb0, hexp, hcoef⟩ := PartF.coef_poly K hK h
    show ∑' j, coef K (fun x => h.eval x) j * ν (cheb K j) = ν h
    simp only [hcoef]
    rw [tsum_eq_sum (s := Finset.range (h.natDegree + 1))]
    · conv_rhs => rw [hexp]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Polynomial.C_mul', map_smul, smul_eq_mul]
    · intro j hj
      have : h.natDegree < j := by simpa using hj
      rw [hb0 j this, zero_mul]


theorem two_of_one (ν : ℝ[X] →ₗ[ℝ] ℝ)
    (h1 : ∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
          |ν h| ≤ c * (q : ℝ) ^ m * cNorm 0 (fun x => h.eval x) (-K) K) :
    ∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 < K ∧ ∀ j : ℕ, 1 ≤ j →
          |ν ((Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X))| ≤ c * (j : ℝ) ^ m := by
  obtain ⟨c, m, K0, hc, hm, hK0, h⟩ := h1
  set K : ℝ := max K0 1 with hKdef
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨c, m, K, hc, hm, hK, fun j hj => ?_⟩
  have hdeg : ((Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X)).natDegree ≤ j := by
    refine (Polynomial.natDegree_comp_le).trans ?_
    have h1 : (Polynomial.C K⁻¹ * X : ℝ[X]).natDegree ≤ 1 := (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
    have h2 : (Chebyshev.T ℝ (j : ℤ)).natDegree = j := by
      rw [Polynomial.Chebyshev.natDegree_T]; simp
    calc _ ≤ (Chebyshev.T ℝ (j : ℤ)).natDegree * 1 := Nat.mul_le_mul le_rfl h1
      _ = j := by rw [h2, mul_one]
  have := h j hj _ hdeg
  have hn : cNorm 0 (fun x => ((Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X)).eval x) (-K0) K0 ≤ 1 := by
    apply cN0_le (by linarith)
    intro x hx
    have hxK : |x / K| ≤ 1 := by
      rw [abs_div, abs_of_pos hK, div_le_one hK]
      exact (abs_le.2 ⟨hx.1, hx.2⟩).trans (le_max_left _ _)
    have hev : ((Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X)).eval x
        = (Chebyshev.T ℝ j).eval (x / K) := by
      simp [Polynomial.eval_comp, div_eq_inv_mul]
    rw [hev]
    have := Polynomial.Chebyshev.T_real_cos (Real.arccos (x / K)) (j : ℤ)
    rw [Real.cos_arccos (abs_le.1 hxK).1 (abs_le.1 hxK).2] at this
    rw [this]
    exact Real.abs_cos_le_one _
  calc _ ≤ _ := this
    _ ≤ c * (j : ℝ) ^ m * 1 := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := mul_one _

theorem tfae_dev (ν : ℝ[X] →ₗ[ℝ] ℝ) :
    List.TFAE
      [∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
          |ν h| ≤ c * (q : ℝ) ^ m * cNorm 0 (fun x => h.eval x) (-K) K,
        ∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 < K ∧ ∀ j : ℕ, 1 ≤ j →
          |ν ((Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X))| ≤ c * (j : ℝ) ^ m,
        ∃! μ : smoothFun →ₗ[ℝ] ℝ, IsCSDistribution μ ∧ ∀ h : ℝ[X], μ (polyFun h) = ν h] := by
  tfae_have 1 → 2 := two_of_one ν
  tfae_have 2 → 3 := by
    rintro ⟨c, m, K, hc, hm, hK, h2⟩
    obtain ⟨μ, hμ, hext⟩ := ext_exists ν c m K hc hm hK h2
    refine ⟨μ, ⟨hμ, hext⟩, fun μ' ⟨h1, h2⟩ => PartG.uniq_cs μ' μ h1 hμ (fun h => by rw [h2, hext])⟩
  tfae_have 3 → 1 := by
    rintro ⟨μ, ⟨hμ, hext⟩, -⟩
    obtain ⟨c, m, K, hc, hm, hK, h⟩ := PartG.one_of_cs μ hμ
    exact ⟨c, m, K, hc, hm, hK, fun q hq h' hh => by rw [← hext]; exact h q hq h' hh⟩
  tfae_finish

end StrongConvS4

namespace StrongConv

theorem tfae_extends_csDistribution_dev (ν : ℝ[X] →ₗ[ℝ] ℝ) :
    List.TFAE
      [∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
          |ν h| ≤ c * (q : ℝ) ^ m * cNorm 0 (fun x => h.eval x) (-K) K,
        ∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 < K ∧ ∀ j : ℕ, 1 ≤ j →
          |ν ((Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X))| ≤ c * (j : ℝ) ^ m,
        ∃! μ : smoothFun →ₗ[ℝ] ℝ, IsCSDistribution μ ∧ ∀ h : ℝ[X], μ (polyFun h) = ν h] := StrongConvS4.tfae_dev ν

end StrongConv

end
end

section
open Polynomial
open StrongConv

theorem solution (ν : ℝ[X] →ₗ[ℝ] ℝ) :
    List.TFAE
      [∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
          |ν h| ≤ c * (q : ℝ) ^ m * cNorm 0 (fun x => h.eval x) (-K) K,
        ∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 < K ∧ ∀ j : ℕ, 1 ≤ j →
          |ν ((Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X))| ≤ c * (j : ℝ) ^ m,
        ∃! μ : smoothFun →ₗ[ℝ] ℝ, IsCSDistribution μ ∧ ∀ h : ℝ[X], μ (polyFun h) = ν h] := by
  apply StrongConv.tfae_extends_csDistribution_dev <;> assumption

end
