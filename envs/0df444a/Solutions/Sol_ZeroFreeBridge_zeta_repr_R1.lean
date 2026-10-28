-- Prove2me | solution 1 for ZeroFreeBridge.zeta_repr_R1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:55:20.253482+00:00
-- url     : https://prove2.me/submissions/750ec7b5-ba19-4367-b91a-0e69f32f6a00

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
/- (R1) DISCHARGE for `zeta_fract_repr_of` -- THE HARD ONE, WORK IN PROGRESS.

   The fractional-part representation on `Re s > 1`:

       riemannZeta s = s/(s-1) - s · ∫_{x>1} {x} x^{-(s+1)} dx  =  stripRHS s.

   Mathlib v4.32.0 has NO such representation (confirmed), so it is built by Abel
   summation (`tendsto_sum_mul_atTop_nhds_one_sub_integral₀`) applied to
   `f x = x^{-s}`, `c 0 = 0`, `c (n+1) = 1`:

     ∑_{k≤n} k^{-s}  →  0 - ∫_{t>1} (-s·t^{-s-1})·⌊t⌋ dt  =  s∫_{t>1} ⌊t⌋ t^{-s-1} dt,
     ⌊t⌋ = t - {t},  s∫_{t>1} t^{-s} dt = s/(s-1)   ⟹   ζ(s) = s/(s-1) - s∫_{t>1}{t}t^{-s-1}.

   STATUS: FULLY ASSEMBLED, CI-green -- no `sorry`. The five analytic Abel-summation
   hypotheses (hf_diff, hf_int, h_lim, hg_dom, hg_int) are discharged on `Re s > 1`
   via a shared derivative helper `hasDerivAt_fPow` and the partial-sum `sum_cOne`;
   part (A) `tendsto_partialSum_zeta` identifies the LHS limit as `riemannZeta s`
   (Complex.summable_one_div_nat_cpow + zeta_eq_tsum... + hasSum_nat_add_iff reindex);
   part (B) evaluates the RHS limit value = `stripRHS s` (⌊t⌋ = t - {t} split,
   `∫_{Ioi 1}(↑t)^{-s} = 1/(s-1)` via integral_Ioi_cpow_of_lt). This discharges the
   R1 input of `zeta_fract_repr_of`. conjecture1_proved = False.
-/


open MeasureTheory Filter Topology Set

namespace ZeroFreeBridge





/-- Shared derivative: for `x ≠ 0`, `d/dx x^{-s} = -s · x^{-s-1}`. -/
private theorem hasDerivAt_fPow {s : ℂ} (hs0 : s ≠ 0) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fPow s) (-s * (x : ℂ) ^ (-s - 1)) x := by
  have h := hasDerivAt_ofReal_cpow_const (x := x) hx (r := -s) (neg_ne_zero.mpr hs0)
  exact h

/-- The coefficient partial sum: `∑_{k=0}^{n} cOne k = n` (cOne kills the `k = 0` term). -/
private theorem sum_cOne (n : ℕ) : ∑ k ∈ Finset.Icc 0 n, cOne k = (n : ℂ) := by
  induction n with
  | zero => simp [cOne]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (Nat.zero_le _), ih]
    have hcm : cOne (m + 1) = 1 := by simp [cOne]
    rw [hcm]; push_cast; ring

/-- (A) The Abel summand `k ↦ k^{-s}·cOne k` (which kills `k = 0`) has partial sums over
    `Icc 0 N` converging to `riemannZeta s`, for `Re s > 1`. -/
private theorem tendsto_partialSum_zeta {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 0 N, fPow s k * cOne k) atTop
      (𝓝 (riemannZeta s)) := by
  -- Summability of the shifted zeta series `∑ 1/(n+1)^s`.
  have hg_sum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have h0 : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    refine ((summable_nat_add_iff 1).mpr h0).congr (fun n => ?_)
    rw [Nat.cast_add_one]
  have hHSg : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]; exact hg_sum.hasSum
  -- Reindex: the summand at `k = n+1` is `1/(n+1)^s`.  Write the argument as the ℕ-cast
  -- `((n+1 : ℕ) : ℝ)` so it matches `(fun k => fPow s k * cOne k) (n+1)` verbatim.
  have hfun : (fun n : ℕ => fPow s ((n + 1 : ℕ) : ℝ) * cOne (n + 1))
      = (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    funext n
    have hc : cOne (n + 1) = 1 := by simp [cOne]
    simp only [fPow, hc, mul_one, one_div]
    rw [← Complex.cpow_neg]
    norm_cast
  have hF1 : HasSum (fun n : ℕ => fPow s ((n + 1 : ℕ) : ℝ) * cOne (n + 1)) (riemannZeta s) := by
    rw [hfun]; exact hHSg
  have hAsum : HasSum (fun k : ℕ => fPow s k * cOne k) (riemannZeta s) := by
    have h := (hasSum_nat_add_iff 1 (f := fun k : ℕ => fPow s k * cOne k)).mp hF1
    simpa [Finset.sum_range_one, cOne] using h
  -- Partial sums over `range` shift to `Icc 0 N = range (N+1)`.
  have hset : ∀ N : ℕ, Finset.Icc 0 N = Finset.range (N + 1) := by
    intro N; ext k; simp
  have htend : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), fPow s k * cOne k) atTop
      (𝓝 (riemannZeta s)) := hAsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine htend.congr (fun N => ?_)
  rw [hset N]





end ZeroFreeBridge


/- (R1) DISCHARGE for `zeta_fract_repr_of` -- THE HARD ONE, WORK IN PROGRESS.

   The fractional-part representation on `Re s > 1`:

       riemannZeta s = s/(s-1) - s · ∫_{x>1} {x} x^{-(s+1)} dx  =  stripRHS s.

   Mathlib v4.32.0 has NO such representation (confirmed), so it is built by Abel
   summation (`tendsto_sum_mul_atTop_nhds_one_sub_integral₀`) applied to
   `f x = x^{-s}`, `c 0 = 0`, `c (n+1) = 1`:

     ∑_{k≤n} k^{-s}  →  0 - ∫_{t>1} (-s·t^{-s-1})·⌊t⌋ dt  =  s∫_{t>1} ⌊t⌋ t^{-s-1} dt,
     ⌊t⌋ = t - {t},  s∫_{t>1} t^{-s} dt = s/(s-1)   ⟹   ζ(s) = s/(s-1) - s∫_{t>1}{t}t^{-s-1}.

   STATUS: FULLY ASSEMBLED, CI-green -- no `sorry`. The five analytic Abel-summation
   hypotheses (hf_diff, hf_int, h_lim, hg_dom, hg_int) are discharged on `Re s > 1`
   via a shared derivative helper `hasDerivAt_fPow` and the partial-sum `sum_cOne`;
   part (A) `tendsto_partialSum_zeta` identifies the LHS limit as `riemannZeta s`
   (Complex.summable_one_div_nat_cpow + zeta_eq_tsum... + hasSum_nat_add_iff reindex);
   part (B) evaluates the RHS limit value = `stripRHS s` (⌊t⌋ = t - {t} split,
   `∫_{Ioi 1}(↑t)^{-s} = 1/(s-1)` via integral_Ioi_cpow_of_lt). This discharges the
   R1 input of `zeta_fract_repr_of`. conjecture1_proved = False.
-/


open MeasureTheory Filter Topology Set

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge











theorem solution {s : ℂ} (hs : 1 < s.re) : riemannZeta s = stripRHS s := by
  have hc0 : cOne 0 = 0 := rfl
  have hs0 : s ≠ 0 := by
    rintro rfl; simp only [Complex.zero_re] at hs; linarith
  -- (hf_diff) differentiability of `x ↦ x^{-s}` on `[1,∞)`.
  have hf_diff : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fPow s) t := by
    intro t ht
    have h1 : (1 : ℝ) ≤ t := ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos h1).ne'
    exact (hasDerivAt_fPow hs0 ht0).differentiableAt
  -- (hf_int) local integrability of the derivative `-s · t^{-s-1}` on `[1,∞)`.
  have hf_int : LocallyIntegrableOn (deriv (fPow s)) (Set.Ici 1) := by
    have hr1 : (-s - 1) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at hre
      linarith
    have hcont : ContinuousOn (fun t : ℝ => -s * (t : ℂ) ^ (-s - 1)) (Set.Ici 1) := by
      apply continuousOn_const.mul
      intro t ht
      have h1 : (1 : ℝ) ≤ t := ht
      have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos h1).ne'
      exact (hasDerivAt_ofReal_cpow_const ht0 hr1).continuousAt.continuousWithinAt
    have heq : Set.EqOn (deriv (fPow s)) (fun t : ℝ => -s * (t : ℂ) ^ (-s - 1)) (Set.Ici 1) := by
      intro t ht
      have h1 : (1 : ℝ) ≤ t := ht
      have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos h1).ne'
      exact (hasDerivAt_fPow hs0 ht0).deriv
    exact (hcont.congr heq).locallyIntegrableOn measurableSet_Ici
  -- (h_lim) `f(n)·∑_{k≤n} cOne k = n^{1-s} → 0` since `Re s > 1`.
  have hne_exp : (1 : ℝ) - s.re ≠ 0 := ne_of_lt (by linarith)
  have hnorm_eq : ∀ n : ℕ, ‖fPow s (n : ℝ) * (n : ℂ)‖ = (n : ℝ) ^ (1 - s.re) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, mul_zero, norm_zero]
      rw [Real.zero_rpow hne_exp]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [norm_mul]
      have hfp : fPow s (n : ℝ) = ((n : ℝ) : ℂ) ^ (-s) := rfl
      rw [hfp, Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.neg_re]
      have hnc : ‖(n : ℂ)‖ = (n : ℝ) := by simp
      rw [hnc, show (1 : ℝ) - s.re = (-s.re) + 1 by ring, Real.rpow_add hnpos, Real.rpow_one]
  have h_lim : Tendsto (fun n : ℕ => fPow s n * ∑ k ∈ Finset.Icc 0 n, cOne k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - s.re)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => x ^ (-(s.re - 1))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by linarith)
      have h2 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have h3 := h1.comp h2
      simpa only [Function.comp_def, neg_sub] using h3
    refine hlim0.congr (fun n => ?_)
    rw [sum_cOne n, hnorm_eq n]
  -- (hg_dom) `deriv f · ⌊t⌋ = -s·t^{-s-1}·⌊t⌋ =O[atTop] t^{-Re s}` (⌊t⌋ ≤ t).
  have hg_dom : (fun t => deriv (fPow s) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cOne k)
      =O[atTop] (fun t : ℝ => t ^ (-s.re)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨‖s‖, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have htpos : (0 : ℝ) < t := by linarith
    have ht0 : t ≠ 0 := htpos.ne'
    rw [sum_cOne ⌊t⌋₊, (hasDerivAt_fPow hs0 ht0).deriv]
    have hfl : ‖(⌊t⌋₊ : ℂ)‖ = (⌊t⌋₊ : ℝ) := by simp
    have hcp : ‖((t : ℝ) : ℂ) ^ (-s - 1)‖ = t ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos]
      congr 1
    have hgnorm : ‖t ^ (-s.re)‖ = t ^ (-s.re) := Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _)
    rw [norm_mul, norm_mul, norm_neg, hcp, hfl, hgnorm]
    have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le htpos.le
    have hpow : t ^ (-s.re - 1) * t = t ^ (-s.re) := by
      have hadd := Real.rpow_add htpos (-s.re - 1) 1
      rw [Real.rpow_one] at hadd
      rw [← hadd]; congr 1; ring
    calc ‖s‖ * t ^ (-s.re - 1) * (⌊t⌋₊ : ℝ)
        ≤ ‖s‖ * t ^ (-s.re - 1) * t := by
          apply mul_le_mul_of_nonneg_left hfloor
          positivity
      _ = ‖s‖ * (t ^ (-s.re - 1) * t) := by ring
      _ = ‖s‖ * t ^ (-s.re) := by rw [hpow]
  -- (hg_int) `t^{-Re s}` is integrable near +∞ since `-Re s < -1`.
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-s.re)) atTop := by
    refine ⟨Set.Ioi 1, Ioi_mem_atTop 1, ?_⟩
    exact integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have habel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀
    (c := cOne) (f := fPow s) hc0 hf_diff hf_int h_lim hg_dom hg_int
  -- (A) LHS partial sums → riemannZeta s; identify the RHS limit value by uniqueness.
  have hval : riemannZeta s
      = 0 - ∫ t in Set.Ioi 1, deriv (fPow s) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cOne k :=
    tendsto_nhds_unique (tendsto_partialSum_zeta hs) habel
  -- (B) evaluate that RHS limit value = stripRHS s.
  have hlt : (-s).re < -1 := by rw [Complex.neg_re]; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
  -- Pointwise: the integrand equals `-s·t^{-s} + s·fractIntegrand` on `Ioi 1` (⌊t⌋ = t - {t}).
  have hIeq : Set.EqOn (fun t : ℝ => deriv (fPow s) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cOne k)
      (fun t : ℝ => -s * ((t : ℝ) : ℂ) ^ (-s) + s * fractIntegrand s t) (Set.Ioi 1) := by
    intro t ht
    have htmem : (1 : ℝ) < t := ht
    have htpos : (0 : ℝ) < t := by linarith
    have ht0 : t ≠ 0 := htpos.ne'
    have htc : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht0
    show deriv (fPow s) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cOne k
        = -s * ((t : ℝ) : ℂ) ^ (-s) + s * fractIntegrand s t
    rw [sum_cOne ⌊t⌋₊, (hasDerivAt_fPow hs0 ht0).deriv]
    have hfloorR : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
      rw [natCast_floor_eq_intCast_floor htpos.le]; exact (Int.self_sub_fract t).symm
    have hfloorC : ((⌊t⌋₊ : ℕ) : ℂ) = ((t : ℝ) : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, hfloorR, Complex.ofReal_sub]
    have hA1 : ((t : ℝ) : ℂ) ^ (-s - 1) * ((t : ℝ) : ℂ) = ((t : ℝ) : ℂ) ^ (-s) := by
      have h := Complex.cpow_add (-s - 1) 1 htc
      rw [Complex.cpow_one] at h
      rw [← h]; congr 1; ring
    have hexp : (-(s + 1) : ℂ) = -s - 1 := by ring
    have hfi : fractIntegrand s t = ((Int.fract t : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (-s - 1) := by
      simp only [fractIntegrand, div_eq_mul_inv]
      rw [← Complex.cpow_neg, hexp]
    rw [hfloorC, hfi, ← hA1]; ring
  rw [hval, MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hIeq]
  -- Integrability of the two summands, then split and evaluate.
  have hint1 : IntegrableOn (fun t : ℝ => -s * ((t : ℝ) : ℂ) ^ (-s)) (Set.Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt hlt one_pos).const_mul (-s)
  have hint_frac : IntegrableOn (fractIntegrand s) (Set.Ioi 1) := by
    have hbound : IntegrableOn (fun t : ℝ => t ^ (-(s.re + 1))) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine Integrable.mono' hbound ?_ ?_
    · apply Measurable.aestronglyMeasurable
      unfold fractIntegrand
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htmem : (1 : ℝ) < t := ht
      have htpos : (0 : ℝ) < t := by linarith
      have hre1 : (s + 1).re = s.re + 1 := by simp [Complex.add_re, Complex.one_re]
      have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
        exact (Int.fract_lt_one t).le
      simp only [fractIntegrand, norm_div]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos, hre1,
          div_le_iff₀ (Real.rpow_pos_of_pos htpos _)]
      have hrw : t ^ (-(s.re + 1)) * t ^ (s.re + 1) = 1 := by
        rw [← Real.rpow_add htpos]; simp
      rw [hrw]; exact hfract
  have hint2 : IntegrableOn (fun t : ℝ => s * fractIntegrand s t) (Set.Ioi 1) :=
    hint_frac.const_mul s
  rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul]
  have hFI : (∫ t in Set.Ioi 1, fractIntegrand s t) = fractIntegral s := rfl
  have hI0 : (∫ t in Set.Ioi 1, ((t : ℝ) : ℂ) ^ (-s)) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt hlt one_pos, Complex.ofReal_one, Complex.one_cpow]
    have hden : (-s) + 1 ≠ 0 := by
      have h : (-s) + 1 = -(s - 1) := by ring
      rw [h]; exact neg_ne_zero.mpr hs1
    field_simp
    ring
  rw [hI0, hFI, stripRHS]
  ring
