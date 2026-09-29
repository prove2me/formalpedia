-- Prove2me | solution 1 for ParticleInARing.energy_two_fold_degenerate
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T19:15:49.649353+00:00
-- url     : https://prove2.me/submissions/164dccf9-af0f-4aeb-b53e-09c382e05cb0

import Mathlib
import Definitions.Def_ParticleInARing_model

open ParticleInARing

theorem W2m_ParticleInARing_eigenstate_periodic (n : ℤ) : IsRingPeriodic (eigenstate n) := by
  intro θ
  simp only [eigenstate]
  congr 1
  rw [show (n : ℂ) * ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
      = (n : ℂ) * (θ : ℂ) * Complex.I + (n : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem W2m_ParticleInARing_hasDerivAt (n : ℤ) (θ : ℝ) :
    HasDerivAt (eigenstate n) ((n : ℂ) * Complex.I * eigenstate n θ) θ := by
  show HasDerivAt (fun θ : ℝ => ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
    Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)) _ θ
  have h1 : HasDerivAt (fun y : ℝ => (n : ℂ) * (y : ℂ) * Complex.I) ((n : ℂ) * Complex.I) θ := by
    exact ((((hasDerivAt_id' θ).ofReal_comp).const_mul (n : ℂ)).mul_const Complex.I).congr_deriv
      (by first | ring1 | (push_cast; ring1) | simp)
  have H := (h1.cexp).const_mul (((1 / Real.sqrt (2 * Real.pi) : ℝ)) : ℂ)
  refine H.congr_deriv ?_
  have e : eigenstate n θ = ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
      Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) := rfl
  rw [e]
  ring

theorem W2m_ParticleInARing_deriv (n : ℤ) :
    deriv (eigenstate n) = fun θ => (n : ℂ) * Complex.I * eigenstate n θ :=
  funext fun θ => (W2m_ParticleInARing_hasDerivAt n θ).deriv

theorem W2m_ParticleInARing_eigenstate_iteratedDeriv_two (n : ℤ) (θ : ℝ) :
    iteratedDeriv 2 (eigenstate n) θ = (-((n : ℂ) ^ 2)) * eigenstate n θ := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, W2m_ParticleInARing_deriv]
  rw [((W2m_ParticleInARing_hasDerivAt n θ).const_mul ((n : ℂ) * Complex.I)).deriv]
  linear_combination (n : ℂ) ^ 2 * eigenstate n θ * Complex.I_sq

theorem W2m_ParticleInARing_eigenstate_isRingEigenstate (hbar m R : ℝ) (hm : m ≠ 0)
    (hR : R ≠ 0) (n : ℤ) :
    IsRingEigenstate hbar m R (energy hbar m R n) (eigenstate n) := by
  refine ⟨?_, W2m_ParticleInARing_eigenstate_periodic n, ?_⟩
  · have h0 : ContDiff ℝ 2 (fun θ : ℝ => (θ : ℂ)) := Complex.ofRealCLM.contDiff
    have H : ContDiff ℝ 2 (fun θ : ℝ => ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
        Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)) :=
      contDiff_const.mul ((contDiff_const.mul h0).mul contDiff_const).cexp
    exact H
  · intro θ
    rw [W2m_ParticleInARing_eigenstate_iteratedDeriv_two]
    simp only [energy]
    push_cast
    ring

theorem W2m_ParticleInARing_energy_two_fold_degenerate (hbar m R : ℝ) (n : ℤ) (hn : n ≠ 0) :
    energy hbar m R (-n) = energy hbar m R n ∧
      LinearIndependent ℂ ![eigenstate n, eigenstate (-n)] := by
  refine ⟨by simp [energy], ?_⟩
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hsp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hc : ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have : (1 / Real.sqrt (2 * Real.pi) : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h0 := congrFun hst 0
  have h1 := congrFun hst (Real.pi / (2 * n))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, eigenstate] at h0 h1
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at h0
  have e1 : (n : ℂ) * ((Real.pi / (2 * n) : ℝ) : ℂ) * Complex.I
      = (Real.pi / 2 : ℂ) * Complex.I := by
    push_cast
    field_simp
  have e2 : ((-n : ℤ) : ℂ) * ((Real.pi / (2 * n) : ℝ) : ℂ) * Complex.I
      = (-(Real.pi / 2 : ℂ)) * Complex.I := by
    push_cast
    field_simp
  rw [e1, e2] at h1
  have x1 : Complex.exp ((Real.pi / 2 : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]; ring
  have x2 : Complex.exp ((-(Real.pi / 2 : ℂ)) * Complex.I) = -Complex.I := by
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two,
      Complex.sin_pi_div_two]; ring
  rw [x1, x2] at h1
  have hA : s + t = 0 := by
    have H : (s + t) * ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 0 := by linear_combination h0
    exact (mul_eq_zero.1 H).resolve_right hc
  have hB : s - t = 0 := by
    have H : (s - t) * (((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 0 := by
      linear_combination h1
    exact (mul_eq_zero.1 H).resolve_right (mul_ne_zero hc Complex.I_ne_zero)
  constructor
  · linear_combination (hA + hB) / 2
  · linear_combination (hA - hB) / 2

theorem W2m_ParticleInARing_eigenstate_orthonormal (j n : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), (starRingEnd ℂ) (eigenstate j θ) * eigenstate n θ =
      if j = n then 1 else 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi' : Real.pi ≠ 0 := hpi.ne'
  have hs : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have key : ∀ θ : ℝ, (starRingEnd ℂ) (eigenstate j θ) * eigenstate n θ =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * Complex.exp ((((n - j : ℤ) : ℂ) * Complex.I) * θ) := by
    intro θ
    simp only [eigenstate, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_intCast,
      Complex.conj_I]
    rw [mul_mul_mul_comm, ← Complex.exp_add, ← Complex.ofReal_mul]
    congr 1
    · congr 1
      rw [div_mul_div_comm, one_mul, ← sq, hs]
    · congr 1
      push_cast
      ring
  simp_rw [key]
  rw [intervalIntegral.integral_const_mul]
  split_ifs with h
  · subst h
    simp
    first | field_simp | skip
  · have hc : (((n - j : ℤ) : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast sub_ne_zero.2 (Ne.symm h)) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    have e : (((n - j : ℤ) : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)
        = ((n - j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
    simp

theorem W2m_ParticleInARing_eigenstate_normalized (n : ℤ) : IsRingNormalized (eigenstate n) := by
  have hpi := Real.pi_pos
  have hpi' : Real.pi ≠ 0 := hpi.ne'
  have hs : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hsp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have key : ∀ θ : ℝ, ‖eigenstate n θ‖ ^ 2 = 1 / (2 * Real.pi) := by
    intro θ
    have e : (n : ℂ) * (θ : ℂ) * Complex.I = (((n : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    simp only [eigenstate, e, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), div_pow, one_pow, hs]
  unfold IsRingNormalized
  simp_rw [key]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp

theorem W2m_ParticleInARing_energy_le_card (hbar m R : ℝ) (hhbar : 0 < hbar) (hm : 0 < m)
    (hR : 0 < R) (N : ℕ) :
    {n : ℤ | energy hbar m R n ≤ energy hbar m R N}.ncard = 2 * N + 1 := by
  have hK : 0 < hbar ^ 2 / (2 * m * R ^ 2) := by positivity
  have e : ∀ z : ℤ, energy hbar m R z = (z : ℝ) ^ 2 * (hbar ^ 2 / (2 * m * R ^ 2)) := by
    intro z; unfold energy; ring
  have key : ∀ n : ℤ, energy hbar m R n ≤ energy hbar m R N ↔ n ^ 2 ≤ (N : ℤ) ^ 2 := by
    intro n
    rw [e, e]
    constructor
    · intro h
      have H : (n : ℝ) ^ 2 ≤ ((N : ℤ) : ℝ) ^ 2 := le_of_mul_le_mul_right h hK
      exact_mod_cast H
    · intro h
      have H : (n : ℝ) ^ 2 ≤ ((N : ℤ) : ℝ) ^ 2 := by exact_mod_cast h
      exact mul_le_mul_of_nonneg_right H hK.le
  have hset : {n : ℤ | energy hbar m R n ≤ energy hbar m R N}
      = ↑(Finset.Icc (-(N : ℤ)) N) := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.coe_Icc, Set.mem_Icc]
    rw [key, sq_le_sq, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (N : ℤ)), abs_le]
  rw [hset, Set.ncard_coe_finset, Int.card_Icc]
  omega

theorem W2m_ParticleInARing_hexpd (c : ℂ) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (c * x)) (Complex.exp (c * θ) * c) θ := by
  exact (((hasDerivAt_id' θ).ofReal_comp.const_mul c).cexp).congr_deriv (by simp)

theorem W2m_ParticleInARing_spectrum_eq_quantized_energies (hbar m R : ℝ) (hhbar : 0 < hbar)
    (hm : 0 < m) (hR : 0 < R) (E : ℝ) :
    (∃ ψ : ℝ → ℂ, (∃ θ : ℝ, ψ θ ≠ 0) ∧ IsRingEigenstate hbar m R E ψ) ↔
      ∃ n : ℤ, E = energy hbar m R n := by
  constructor
  · rintro ⟨ψ, ⟨θ₁, hθ₁⟩, hψ⟩
    obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = -(2 * m * R ^ 2 * E / hbar ^ 2) := ⟨_, rfl⟩
    have hK : 0 < hbar ^ 2 / (2 * m * R ^ 2) := by positivity
    have hc : ((-(hbar ^ 2 / (2 * m * R ^ 2)) : ℝ) : ℂ) ≠ 0 := by
      have : (-(hbar ^ 2 / (2 * m * R ^ 2)) : ℝ) ≠ 0 := by
        intro h0; linarith
      exact_mod_cast this
    have hcl : ((-(hbar ^ 2 / (2 * m * R ^ 2)) : ℝ) : ℂ) * (lam : ℂ) = (E : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [hlam]
      have h1 : hbar ≠ 0 := hhbar.ne'
      have h2 : m ≠ 0 := hm.ne'
      have h3 : R ≠ 0 := hR.ne'
      first | (field_simp; ring1) | field_simp
    have hode : ∀ θ, deriv (deriv ψ) θ = (lam : ℂ) * ψ θ := by
      intro θ
      have H := hψ.schrodinger θ
      rw [iteratedDeriv_succ, iteratedDeriv_one] at H
      apply mul_left_cancel₀ hc
      rw [H, ← mul_assoc, hcl]
    have hd1 : Differentiable ℝ ψ :=
      hψ.smooth.differentiable (by first | norm_num | exact one_le_two | simp)
    have hd2 : Differentiable ℝ (deriv ψ) := by
      have H := hψ.smooth.differentiable_iteratedDeriv 1
        (by first | norm_num | exact_mod_cast one_lt_two | simp)
      rwa [iteratedDeriv_one] at H
    have hper : ∀ θ, ψ (θ + 2 * Real.pi) = ψ θ := hψ.periodic
    have hper' : ∀ θ, deriv ψ (θ + 2 * Real.pi) = deriv ψ θ := by
      intro θ
      have e : (fun x => ψ (x + 2 * Real.pi)) = ψ := funext hper
      have H := deriv_comp_add_const (f := ψ) (a := 2 * Real.pi) (x := θ)
      rw [e] at H
      exact H.symm
    by_cases hl : lam = 0
    · refine ⟨0, ?_⟩
      rw [hlam] at hl
      have h2 : 2 * m * R ^ 2 * E / hbar ^ 2 = 0 := by linarith
      have h1 : 2 * m * R ^ 2 * E = 0 := by
        rcases div_eq_zero_iff.1 h2 with h3 | h3
        · exact h3
        · exact absurd h3 (by positivity)
      have hE : E = 0 := (mul_eq_zero.1 h1).resolve_left (by positivity)
      rw [hE]
      simp [energy]
    · obtain ⟨ω, hω⟩ := IsAlgClosed.exists_pow_nat_eq ((lam : ℝ) : ℂ) (by norm_num : 0 < 2)
      have hω0 : ω ≠ 0 := by
        rintro rfl
        apply hl
        have : ((lam : ℝ) : ℂ) = 0 := by rw [← hω]; ring
        exact_mod_cast this
      have hF : ∀ θ : ℝ, HasDerivAt (fun x : ℝ => (deriv ψ x - ω * ψ x) * Complex.exp (ω * x))
          0 θ := by
        intro θ
        refine (((hd2 θ).hasDerivAt.fun_sub ((hd1 θ).hasDerivAt.const_mul ω)).fun_mul
          (W2m_ParticleInARing_hexpd ω θ)).congr_deriv ?_
        rw [hode θ]
        linear_combination (-(ψ θ * Complex.exp (ω * θ))) * hω
      have hG : ∀ θ : ℝ, HasDerivAt (fun x : ℝ => (deriv ψ x + ω * ψ x) * Complex.exp ((-ω) * x))
          0 θ := by
        intro θ
        refine (((hd2 θ).hasDerivAt.fun_add ((hd1 θ).hasDerivAt.const_mul ω)).fun_mul
          (W2m_ParticleInARing_hexpd (-ω) θ)).congr_deriv ?_
        rw [hode θ]
        linear_combination (-(ψ θ * Complex.exp ((-ω) * θ))) * hω
      have hFc := is_const_of_deriv_eq_zero (fun θ => (hF θ).differentiableAt)
        (fun θ => (hF θ).deriv)
      have hGc := is_const_of_deriv_eq_zero (fun θ => (hG θ).differentiableAt)
        (fun θ => (hG θ).deriv)
      have hu : ∀ θ : ℝ, (deriv ψ θ - ω * ψ θ) * Complex.exp (ω * θ)
          = deriv ψ 0 - ω * ψ 0 := by
        intro θ
        have H := hFc θ 0
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at H
        exact H
      have hv : ∀ θ : ℝ, (deriv ψ θ + ω * ψ θ) * Complex.exp ((-ω) * θ)
          = deriv ψ 0 + ω * ψ 0 := by
        intro θ
        have H := hGc θ 0
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at H
        exact H
      have hper0 : ψ (2 * Real.pi) = ψ 0 := by simpa using hper 0
      have hper0' : deriv ψ (2 * Real.pi) = deriv ψ 0 := by simpa using hper' 0
      have hu2 := hu (2 * Real.pi)
      have hv2 := hv (2 * Real.pi)
      rw [hper0, hper0'] at hu2 hv2
      -- conclude ω = k * I for some integer k
      have hkey : ∃ k : ℤ, ω = k * Complex.I ∨ ω = -(k * Complex.I) := by
        by_cases hu0 : deriv ψ 0 - ω * ψ 0 = 0
        · by_cases hv0 : deriv ψ 0 + ω * ψ 0 = 0
          · exfalso
            apply hθ₁
            have h1 := hu θ₁
            have h2 := hv θ₁
            rw [hu0] at h1
            rw [hv0] at h2
            have e1 : deriv ψ θ₁ - ω * ψ θ₁ = 0 := by
              rcases mul_eq_zero.1 h1 with h | h
              · exact h
              · exact absurd h (Complex.exp_ne_zero _)
            have e2 : deriv ψ θ₁ + ω * ψ θ₁ = 0 := by
              rcases mul_eq_zero.1 h2 with h | h
              · exact h
              · exact absurd h (Complex.exp_ne_zero _)
            have e3 : (2 * ω) * ψ θ₁ = 0 := by linear_combination e2 - e1
            rcases mul_eq_zero.1 e3 with h | h
            · exact absurd h (mul_ne_zero two_ne_zero hω0)
            · exact h
          · have H : Complex.exp ((-ω) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
              exact (mul_right_eq_self₀.1 hv2).resolve_right hv0
            obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 H
            refine ⟨k, Or.inr ?_⟩
            have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
            push_cast at hk
            have : (2 * (Real.pi : ℂ)) * (-ω - k * Complex.I) = 0 := by
              linear_combination hk
            rcases mul_eq_zero.1 this with h | h
            · exact absurd h (mul_ne_zero two_ne_zero hpi)
            · linear_combination -h
        · have H : Complex.exp (ω * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
            exact (mul_right_eq_self₀.1 hu2).resolve_right hu0
          obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 H
          refine ⟨k, Or.inl ?_⟩
          have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
          push_cast at hk
          have : (2 * (Real.pi : ℂ)) * (ω - k * Complex.I) = 0 := by
            linear_combination hk
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h (mul_ne_zero two_ne_zero hpi)
          · linear_combination h
      obtain ⟨k, hk⟩ := hkey
      have hlk : ((lam : ℝ) : ℂ) = ((-(k : ℝ) ^ 2 : ℝ) : ℂ) := by
        rw [← hω]
        rcases hk with hk | hk
        · rw [hk]; push_cast; linear_combination ((k : ℂ) ^ 2) * Complex.I_sq
        · rw [hk]; push_cast; linear_combination ((k : ℂ) ^ 2) * Complex.I_sq
      have hlk' : lam = -(k : ℝ) ^ 2 := by exact_mod_cast hlk
      refine ⟨k, ?_⟩
      rw [hlam] at hlk'
      unfold energy
      have h1 : hbar ≠ 0 := hhbar.ne'
      have h2 : 2 * m * R ^ 2 ≠ 0 := by positivity
      have h3 : 2 * m * R ^ 2 * E / hbar ^ 2 = (k : ℝ) ^ 2 := by linarith
      rw [div_eq_iff (by positivity)] at h3
      rw [eq_div_iff h2]
      linarith
  · rintro ⟨n, rfl⟩
    have hc : ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
      have : (1 / Real.sqrt (2 * Real.pi) : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    refine ⟨eigenstate n, ⟨0, ?_⟩,
      W2m_ParticleInARing_eigenstate_isRingEigenstate hbar m R hm.ne' hR.ne' n⟩
    simp only [eigenstate, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    exact hc

theorem solution (hbar m R : ℝ) (n : ℤ) (hn : n ≠ 0) :
    energy hbar m R (-n) = energy hbar m R n ∧
      LinearIndependent ℂ ![eigenstate n, eigenstate (-n)] := by
  apply W2m_ParticleInARing_energy_two_fold_degenerate <;> assumption
