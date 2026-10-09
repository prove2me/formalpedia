-- Prove2me | solution 1 for SWPort.Davenport.neg_logDeriv_trivChar_le_pole
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:24:49.588414+00:00
-- url     : https://prove2.me/submissions/e043bc62-29c4-4721-88f2-1c8ceb770b88

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001

section
-- module Solutions.Artin.SW.Thm.Zeta23_WeilEF_zeta_logDeriv_partial_fraction
alias SWPort.Zeta23.WeilEF.zeta_logDeriv_partial_fraction := SWPort.Z.Zeta23.WeilEF.zeta_logDeriv_partial_fraction
end

section
-- module Solutions.Artin.SW.Thm.Davenport_neg_logDeriv_trivChar_le_pole
namespace SWPort
/-! Ported from prove2.me: `Davenport.neg_logDeriv_trivChar_le_pole` (e7d1b484-b924-4238-b7fe-e79d905bd6c1, statement by alya); proof = accepted sketch submission 94a9e456-63c4-4b18-9444-65c7969a7dab by alya. -/








/-!
# `-L'/L` for the principal character, with the pole subtracted

We prove
`∃ c > 0, ∀ q (s : ℂ), 1 < Re s ≤ 2 → Re (-L'/L)(s, χ₀) ≤ Re (1/(s-1)) + c log (q(|Im s|+2))`.

The proof has three independent parts.

* For `|Im s| ≥ 6` the platform theorem `Zeta23.WeilEF.zeta_logDeriv_partial_fraction`
  (Landau's partial-fraction expansion of `ζ'/ζ`) gives `-Re ζ'/ζ(s) ≤ C log(|Im s|+3)`,
  because every zero `ρ` occurring in the expansion has `Re ρ < 1 < Re s` and therefore
  contributes a nonnegative `Re 1/(s-ρ)`.
* For `|Im s| ≤ 6` the function `-ζ'/ζ(s) - 1/(s-1)` extends continuously to the compact
  rectangle `{1 ≤ Re s ≤ 2, |Im s| ≤ 6}` (Mathlib's `LFunctionTrivChar₁` for `q = 1`),
  hence is bounded there.
* Passing from `ζ` to `L(·, χ₀)` removes the Euler factors at the primes dividing `q`;
  their logarithmic derivative is bounded in norm by `Σ_{p ∣ q} log p ≤ log q`.
-/

set_option linter.unusedVariables false

open Complex

namespace Sol

/-- `Re (1/w) ≥ 0` when `Re w > 0`. -/
private lemma inv_re_nonneg_p0 {w : ℂ} (h : 0 < w.re) : 0 ≤ (w⁻¹).re := by
  rw [Complex.inv_re]
  exact div_nonneg h.le (Complex.normSq_nonneg _)

/-- A zero of `ζ` has real part `< 1`. -/
private lemma zero_re_lt_one_p0 {ρ : ℂ} (h : riemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra hc
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) h

/-- Large-height bound: `-Re ζ'/ζ(s) ≤ C log(|t|+3)` for `1 < σ ≤ 2`, `|t| ≥ 6`. -/
private lemma zeta_high_p0 :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → 6 ≤ |s.im| →
      (-(deriv riemannZeta s / riemannZeta s)).re ≤ C * Real.log (|s.im| + 3) := by
  obtain ⟨C, hC, H⟩ := Zeta23.WeilEF.zeta_logDeriv_partial_fraction
  refine ⟨C, hC, fun s h1 h2 h6 => ?_⟩
  obtain ⟨Z, hZset, -, hZbnd⟩ := H s.im h6
  have hball : s ∈ Metric.closedBall (2 + (s.im : ℂ) * I) (3/2) := by
    have he : s - (2 + (s.im : ℂ) * I) = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [Metric.mem_closedBall, Complex.dist_eq, he, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have hsz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt h1)
  have key := hZbnd s hball hsz
  -- the zero sum has nonnegative real part
  have hsum : 0 ≤ (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun ρ hρ => ?_
    have hρ0 : riemannZeta ρ = 0 := by
      have : ρ ∈ {ρ ∈ Metric.closedBall (2 + (s.im : ℂ) * I) (22/25 * (91/50)) |
          riemannZeta ρ = 0} := by rw [← hZset]; exact_mod_cast hρ
      exact this.2
    have hre : 0 < (s - ρ).re := by
      have := zero_re_lt_one_p0 hρ0
      simp only [Complex.sub_re]
      linarith
    have : ((analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)).re
        = (analyticOrderNatAt riemannZeta ρ : ℝ) * ((s - ρ)⁻¹).re := by
      rw [div_eq_mul_inv]
      simp [Complex.mul_re]
    rw [this]
    exact mul_nonneg (Nat.cast_nonneg _) (inv_re_nonneg_p0 hre)
  have habs : |(logDeriv riemannZeta s
      - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)).re|
      ≤ C * Real.log (|s.im| + 3) := (Complex.abs_re_le_norm _).trans key
  have h := abs_le.mp habs
  rw [Complex.sub_re] at h
  rw [show (-(deriv riemannZeta s / riemannZeta s)) = -(logDeriv riemannZeta s) by
    rw [logDeriv_apply], Complex.neg_re]
  linarith [h.1, hsum]

/-- Small-height bound via compactness of `{1 ≤ σ ≤ 2, |t| ≤ 6}`. -/
private lemma zeta_low : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 6 →
    (-(deriv riemannZeta s / riemannZeta s)).re ≤ (1 / (s - 1)).re + C := by
  set K : Set ℂ :=
    (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) '' (Set.Icc (1:ℝ) 2 ×ˢ Set.Icc (-6:ℝ) 6) with hKdef
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hzeta : DirichletCharacter.LFunctionTrivChar 1 = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq (χ := 1)
  have hsub : K ⊆ {s : ℂ | s = 1 ∨ DirichletCharacter.LFunctionTrivChar 1 s ≠ 0} := by
    rintro _ ⟨p, hp, rfl⟩
    refine Or.inr ?_
    rw [hzeta]
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simpa using hp.1.1
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn
    ((DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁ 1).mono hsub)
  refine ⟨max C0 0, le_max_right _ _, fun s h1 h2 h6 => ?_⟩
  have hsK : s ∈ K := by
    refine ⟨(s.re, s.im), ⟨⟨le_of_lt h1, h2⟩, ?_⟩, ?_⟩
    · exact ⟨by linarith [abs_le.mp h6 |>.1], (abs_le.mp h6).2⟩
    · exact Complex.re_add_im s
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt h1)
  have hsub1 : s - 1 ≠ 0 := sub_ne_zero_of_ne hs1
  have hF : DirichletCharacter.LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
    simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
    rw [hzeta]
  have hdF : deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s
      = (s - 1) * deriv riemannZeta s + riemannZeta s := by
    rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs1, hzeta]
  have hkey : -deriv riemannZeta s / riemannZeta s
      = (-deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s
          / DirichletCharacter.LFunctionTrivChar₁ 1 s) + 1 / (s - 1) := by
    rw [hdF, hF]
    field_simp
    ring
  have hbound := hC0 s hsK
  have hre := (Complex.re_le_norm (-deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s
      / DirichletCharacter.LFunctionTrivChar₁ 1 s)).trans hbound
  rw [show (-(deriv riemannZeta s / riemannZeta s))
      = -deriv riemannZeta s / riemannZeta s by rw [neg_div], hkey, Complex.add_re]
  have : C0 ≤ max C0 0 := le_max_left _ _
  linarith

private lemma log_two_le_p0 (t : ℝ) : Real.log 2 ≤ Real.log (|t| + 2) :=
  Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])

private lemma log_two_pos_p0 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

private lemma log_three_le_p0 (t : ℝ) : Real.log (|t| + 3) ≤ 2 * Real.log (|t| + 2) := by
  have h0 := abs_nonneg t
  have h1 : |t| + 3 ≤ (|t| + 2) ^ 2 := by nlinarith
  have h2 : Real.log (|t| + 3) ≤ Real.log ((|t| + 2) ^ 2) :=
    Real.log_le_log (by linarith) h1
  rwa [Real.log_pow] at h2
  
private lemma pole_re_nonneg {s : ℂ} (h : 1 < s.re) : 0 ≤ ((1:ℂ) / (s - 1)).re := by
  rw [one_div]
  refine inv_re_nonneg_p0 ?_
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- The full pole-corrected bound for `-ζ'/ζ` on the strip `1 < σ ≤ 2`. -/
private lemma zeta_pole : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
    (-(deriv riemannZeta s / riemannZeta s)).re
      ≤ ((1:ℂ) / (s - 1)).re + C * Real.log (|s.im| + 2) := by
  obtain ⟨Ch, hCh, Hh⟩ := zeta_high_p0
  obtain ⟨Cl, hCl, Hl⟩ := zeta_low
  refine ⟨2 * Ch + Cl / Real.log 2, by positivity, fun s h1 h2 => ?_⟩
  have hl2 := log_two_pos_p0
  have hlt := log_two_le_p0 s.im
  have hltpos : 0 < Real.log (|s.im| + 2) := lt_of_lt_of_le hl2 hlt
  have hpole := pole_re_nonneg h1
  rcases le_or_gt 6 |s.im| with h6 | h6
  · have h := Hh s h1 h2 h6
    have h3 := log_three_le_p0 s.im
    have hCl' : 0 ≤ Cl / Real.log 2 * Real.log (|s.im| + 2) := by positivity
    nlinarith [hCh.le, h, h3, hpole, hCl']
  · have h := Hl s h1 h2 h6.le
    have hb : Cl ≤ Cl / Real.log 2 * Real.log (|s.im| + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      nlinarith [hCl]
    have : 0 ≤ 2 * Ch * Real.log (|s.im| + 2) := by positivity
    linarith

section EulerFactors

variable {p : ℕ} {s : ℂ}

private lemma pow_le_half (hp : 2 ≤ p) (hs : 1 < s.re) : (p:ℝ) ^ (-s.re) ≤ 1/2 := by
  have hp1 : (1:ℝ) < (p:ℝ) := by
    have : (1:ℕ) < p := by omega
    exact_mod_cast this
  have h1 : (p:ℝ) ^ (1:ℝ) ≤ (p:ℝ) ^ s.re := by
    exact Real.rpow_le_rpow_of_exponent_le hp1.le hs.le
  rw [Real.rpow_one] at h1
  have h2 : (2:ℝ) ≤ (p:ℝ) ^ s.re := le_trans (by exact_mod_cast hp) h1
  rw [Real.rpow_neg (by positivity), inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

private lemma norm_cpow_neg (hp : 2 ≤ p) (s : ℂ) : ‖(p:ℂ) ^ (-s)‖ = (p:ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]

private lemma diffAt (hp : 2 ≤ p) (s : ℂ) : DifferentiableAt ℂ (fun z : ℂ => 1 - (p:ℂ) ^ (-z)) s := by
  have hp0 : ((p:ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  exact (differentiableAt_const _).sub ((differentiableAt_id.neg).const_cpow (Or.inl hp0))

private lemma factor_ne_zero (hp : 2 ≤ p) (hs : 1 < s.re) : (1:ℂ) - (p:ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : ‖(p:ℂ) ^ (-s)‖ = 1 := by
    have : (p:ℂ) ^ (-s) = 1 := by linear_combination -h
    rw [this]; simp
  rw [norm_cpow_neg hp] at h1
  have := pow_le_half hp hs
  rw [h1] at this
  norm_num at this

private lemma norm_factor_ge (hp : 2 ≤ p) (hs : 1 < s.re) :
    (p:ℝ) ^ (-s.re) ≤ ‖(1:ℂ) - (p:ℂ) ^ (-s)‖ := by
  have h := pow_le_half hp hs
  have hge : 1 - ‖(p:ℂ) ^ (-s)‖ ≤ ‖(1:ℂ) - (p:ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((p:ℂ) ^ (-s))
    simpa using this
  rw [norm_cpow_neg hp] at hge
  linarith

private lemma logDeriv_factor (hp : 2 ≤ p) (hs : 1 < s.re) :
    ‖logDeriv (fun z : ℂ => 1 - (p:ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  have hp0 : ((p:ℂ)) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hd : deriv (fun z : ℂ => 1 - (p:ℂ) ^ (-z)) s = Complex.log (p:ℂ) * (p:ℂ) ^ (-s) := by
    have h1 : HasStrictDerivAt (fun z : ℂ => -z) (-1) s := (hasStrictDerivAt_id s).neg
    have h2 := (h1.const_cpow (c := (p:ℂ)) (Or.inl hp0)).hasDerivAt
    have h3 := h2.const_sub (1 : ℂ)
    have := h3.deriv
    rw [this]; ring
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast Nat.one_le_of_lt hp
  have hlogn : ‖Complex.log (p:ℂ)‖ = Real.log p := by
    rw [show ((p:ℂ)) = ((p:ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hp1)]
  have hx := pow_le_half hp hs
  have hy := norm_factor_ge hp hs
  have hxpos : (0:ℝ) < (p:ℝ) ^ (-s.re) := Real.rpow_pos_of_pos (by linarith) _
  rw [logDeriv_apply, hd, norm_div, norm_mul, hlogn, norm_cpow_neg hp]
  rw [div_le_iff₀ (lt_of_lt_of_le hxpos hy)]
  have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
  nlinarith [hy, hxpos, hlp]

end EulerFactors

/-- Removing the Euler factors of the principal character costs at most `log q`. -/
private lemma euler (q : ℕ) [NeZero q] (s : ℂ) (hs : 1 < s.re) :
    (-(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
        / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)).re
      ≤ (-(deriv riemannZeta s / riemannZeta s)).re + Real.log q := by
  classical
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hprime : ∀ p ∈ q.primeFactors, 2 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le
  set P : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - (p:ℂ) ^ (-z)) with hP
  have hzs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hPs : P s ≠ 0 := by
    rw [hP, Finset.prod_ne_zero_iff]
    exact fun p hp => factor_ne_zero (hprime p hp) hs
  have hdP : DifferentiableAt ℂ P s :=
    DifferentiableAt.fun_finsetProd (fun p hp => diffAt (hprime p hp) s)
  have hdz : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta (by intro h; rw [h] at hs; simp at hs)
  -- the factorisation holds on a neighbourhood of `s`
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : DirichletCharacter.LFunctionTrivChar q =ᶠ[nhds s] fun z => P z * riemannZeta z := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    refine DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta ?_
    intro h
    rw [h] at hz
    simp at hz
  have hlog : logDeriv (DirichletCharacter.LFunctionTrivChar q) s
      = logDeriv P s + logDeriv riemannZeta s := by
    rw [logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds, ← logDeriv_apply,
      logDeriv_mul s hPs hzs hdP hdz]
  -- bound the Euler-factor part
  have hsum : logDeriv P s = ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p:ℂ) ^ (-z)) s :=
    logDeriv_prod (fun p hp => factor_ne_zero (hprime p hp) hs)
      (fun p hp => diffAt (hprime p hp) s)
  have hbound : ‖logDeriv P s‖ ≤ Real.log q := by
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun p hp => logDeriv_factor (hprime p hp) hs)).trans ?_
    have hlogprod : ∑ p ∈ q.primeFactors, Real.log p
        = Real.log (∏ p ∈ q.primeFactors, (p:ℝ)) := by
      rw [Real.log_prod]
      intro p hp
      have := hprime p hp
      exact ne_of_gt (Nat.cast_pos.mpr (by omega))
    rw [hlogprod]
    refine Real.log_le_log (Finset.prod_pos (fun p hp =>
      Nat.cast_pos.mpr (by have := hprime p hp; omega))) ?_
    have hdvd : (∏ p ∈ q.primeFactors, p) ∣ q := Nat.prod_primeFactors_dvd q
    have hle : (∏ p ∈ q.primeFactors, p) ≤ q := Nat.le_of_dvd hq0 hdvd
    calc (∏ p ∈ q.primeFactors, (p:ℝ)) = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (q : ℝ) := by exact_mod_cast hle
  have hkey : (-(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
      / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)).re
      = -(logDeriv P s).re + (-(deriv riemannZeta s / riemannZeta s)).re := by
    have : (deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
        / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)
        = logDeriv (DirichletCharacter.LFunctionTrivChar q) s := by
      rw [logDeriv_apply]
    rw [this, hlog]
    simp [logDeriv_apply, Complex.neg_re, Complex.add_re]
    ring
  rw [hkey]
  have := (neg_le_abs (logDeriv P s).re).trans ((Complex.abs_re_le_norm _).trans hbound)
  linarith


end Sol

theorem _root_.SWPort.Davenport.neg_logDeriv_trivChar_le_pole_oai : ∃ c : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q] (s : ℂ), 1 < s.re → s.re ≤ 2 →
      (-(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
          / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)).re
        ≤ (1 / (s - 1)).re + c * Real.log ((q : ℝ) * (|s.im| + 2)) := by
  obtain ⟨C, hC, HC⟩ := Sol.zeta_pole
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun q _ s h1 h2 => ?_⟩
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have habs := abs_nonneg s.im
  have hsplit : Real.log ((q : ℝ) * (|s.im| + 2)) = Real.log q + Real.log (|s.im| + 2) :=
    Real.log_mul (by linarith) (by linarith)
  have hlogt : 0 < Real.log (|s.im| + 2) :=
    lt_of_lt_of_le Sol.log_two_pos_p0 (Sol.log_two_le_p0 s.im)
  have h1' := Sol.euler q s h1
  have h2' := HC s h1 h2
  rw [hsplit]
  have e1 : C * Real.log (|s.im| + 2) ≤ max C 1 * Real.log (|s.im| + 2) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hlogt.le
  have e2 : Real.log q ≤ max C 1 * Real.log q :=
    le_mul_of_one_le_left hlogq (le_max_right _ _)
  linarith

end SWPort
end

theorem solution : type_of% @SWPort.Davenport.neg_logDeriv_trivChar_le_pole_oai := @SWPort.Davenport.neg_logDeriv_trivChar_le_pole_oai
