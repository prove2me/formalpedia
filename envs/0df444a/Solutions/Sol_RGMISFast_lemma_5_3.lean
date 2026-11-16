-- Prove2me | solution 1 for RGMISFast.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T23:56:17.780952+00:00
-- url     : https://prove2.me/submissions/d2fdd38f-c546-4555-b8bc-a153967ff4fa

import Theorems.Thm_RGMISFast_Ncount_measurable
import Theorems.Thm_RGMISFast_prescribed_extension_drift
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

set_option autoImplicit false
namespace PrescribedDecay

open Set

/-- The negative inverse power converts the nonlinear differential inequality
into a lower bound on its derivative. -/
theorem inverse_power_derivative_lower (y v c : ℝ) (k : ℕ)
    (hy : 0 < y) (hk : 0 < k)
    (hv : v ≤ -(k : ℝ) * c * y ^ (1 + (k : ℝ)⁻¹)) :
    c ≤ v * (-(k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hcoeff : (-(k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr hkpos.le))
      (Real.rpow_nonneg hy.le _)
  have hmul := mul_le_mul_of_nonpos_right hv hcoeff
  have hidentity : (-(k : ℝ) * c * y ^ (1 + (k : ℝ)⁻¹)) *
      ((-(k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1)) = c := by
    calc
      _ = (k : ℝ) * (k : ℝ)⁻¹ * c *
          (y ^ (1 + (k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1)) := by ring
      _ = c := by
        rw [← Real.rpow_add hy]
        have hexp : (1 + (k : ℝ)⁻¹) + (-(k : ℝ)⁻¹ - 1) = 0 := by ring
        rw [hexp, Real.rpow_zero, mul_inv_cancel₀ hkpos.ne']
        ring
  rw [hidentity] at hmul
  nlinarith [hmul]

/-- Integration with an arbitrary differentiable clock. This stronger form
retains the initial value and requires strict positivity of the function. -/
theorem inverse_power_clock_growth
    (f f' q q' : ℝ → ℝ) (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hfcont : ContinuousOn f (Icc 0 a)) (hqcont : ContinuousOn q (Icc 0 a))
    (hfpos : ∀ t ∈ Icc 0 a, 0 < f t)
    (hfderiv : ∀ t ∈ Ioo 0 a, HasDerivAt f (f' t) t)
    (hqderiv : ∀ t ∈ Ioo 0 a, HasDerivAt q (q' t) t)
    (hode : ∀ t ∈ Ioo 0 a,
      f' t ≤ -(k : ℝ) * q' t * f t ^ (1 + (k : ℝ)⁻¹)) :
    f 0 ^ (-(k : ℝ)⁻¹) + (q a - q 0) ≤ f a ^ (-(k : ℝ)⁻¹) := by
  let F : ℝ → ℝ := fun t ↦ f t ^ (-(k : ℝ)⁻¹) - q t
  have hFcont : ContinuousOn F (Icc 0 a) :=
    (hfcont.rpow_const (fun t ht ↦ Or.inl (hfpos t ht).ne')).sub hqcont
  have hFderiv (t : ℝ) (ht : t ∈ Ioo 0 a) :
      HasDerivAt F
        (f' t * (-(k : ℝ)⁻¹) * f t ^ (-(k : ℝ)⁻¹ - 1) - q' t) t :=
    ((hfderiv t ht).rpow_const (Or.inl (hfpos t ⟨ht.1.le, ht.2.le⟩).ne')).sub
      (hqderiv t ht)
  have hmono : MonotoneOn F (Icc 0 a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a) hFcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hFderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hFderiv t ht).deriv]
      have h := inverse_power_derivative_lower (f t) (f' t) (q' t) k
        (hfpos t ⟨ht.1.le, ht.2.le⟩) hk (hode t ht)
      linarith
  have hends := hmono (show (0 : ℝ) ∈ Icc 0 a from ⟨le_rfl, ha.le⟩)
    (show a ∈ Icc 0 a from ⟨ha.le, le_rfl⟩) ha.le
  dsimp [F] at hends
  linarith

/-- Turning a lower bound on a negative inverse power back into an ordinary
power upper bound. -/
theorem le_inverse_pow_of_inverse_power_lower (y L : ℝ) (k : ℕ)
    (hy : 0 < y) (hL : 0 < L) (hk : 0 < k)
    (h : L ≤ y ^ (-(k : ℝ)⁻¹)) :
    y ≤ (L⁻¹) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hh := Real.rpow_le_rpow_of_nonpos hL h (neg_nonpos.mpr hkpos.le)
  rw [← Real.rpow_mul hy.le] at hh
  have hexp : (-(k : ℝ)⁻¹) * (-(k : ℝ)) = 1 := by field_simp
  rw [hexp, Real.rpow_one, Real.rpow_neg hL.le, Real.rpow_natCast, ← inv_pow] at hh
  exact hh

/-- The nonnegative version needs no strict positivity assumption: the ODE
makes `f` nonincreasing, so either the endpoint is zero or the whole interval
has positive values and the inverse-power argument applies. -/
theorem power_decay_bound_with_clock
    (f f' q q' : ℝ → ℝ) (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hfcont : ContinuousOn f (Icc 0 a)) (hqcont : ContinuousOn q (Icc 0 a))
    (hfnonneg : ∀ t ∈ Icc 0 a, 0 ≤ f t)
    (hqnonneg : ∀ t ∈ Ioo 0 a, 0 ≤ q' t)
    (hfderiv : ∀ t ∈ Ioo 0 a, HasDerivAt f (f' t) t)
    (hqderiv : ∀ t ∈ Ioo 0 a, HasDerivAt q (q' t) t)
    (hode : ∀ t ∈ Ioo 0 a,
      f' t ≤ -(k : ℝ) * q' t * f t ^ (1 + (k : ℝ)⁻¹))
    (hclock : 0 < q a - q 0) :
    f a ≤ ((q a - q 0)⁻¹) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hazero : (0 : ℝ) ∈ Icc 0 a := ⟨le_rfl, ha.le⟩
  have haend : a ∈ Icc 0 a := ⟨ha.le, le_rfl⟩
  have hanti : AntitoneOn f (Icc 0 a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 a) hfcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hfderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hfderiv t ht).deriv]
      have hnonpos : -(k : ℝ) * q' t * f t ^ (1 + (k : ℝ)⁻¹) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkpos.le) (hqnonneg t ht))
          (Real.rpow_nonneg (hfnonneg t ⟨ht.1.le, ht.2.le⟩) _)
      exact (hode t ht).trans hnonpos
  by_cases hzero : f a = 0
  · rw [hzero]
    exact pow_nonneg (inv_nonneg.mpr hclock.le) _
  · have hfapos : 0 < f a := lt_of_le_of_ne (hfnonneg a haend) (Ne.symm hzero)
    have hfpos : ∀ t ∈ Icc 0 a, 0 < f t := by
      intro t ht
      exact hfapos.trans_le (hanti ht haend ht.2)
    have hgrowth := inverse_power_clock_growth f f' q q' a k ha hk
      hfcont hqcont hfpos hfderiv hqderiv hode
    have hlow : q a - q 0 ≤ f a ^ (-(k : ℝ)⁻¹) := by
      have hinit := Real.rpow_nonneg (hfnonneg 0 hazero) (-(k : ℝ)⁻¹)
      linarith
    exact le_inverse_pow_of_inverse_power_lower (f a) (q a - q 0) k
      hfapos hclock hk hlow

/-- The autonomous version after the time change `s = -log (1-t)`. -/
theorem power_decay_bound
    (g g' : ℝ → ℝ) (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hgcont : ContinuousOn g (Icc 0 a))
    (hgnonneg : ∀ t ∈ Icc 0 a, 0 ≤ g t)
    (hgderiv : ∀ t ∈ Ioo 0 a, HasDerivAt g (g' t) t)
    (hode : ∀ t ∈ Ioo 0 a,
      g' t ≤ -(k : ℝ) / Real.exp 1 * g t ^ (1 + (k : ℝ)⁻¹)) :
    g a ≤ (Real.exp 1 / a) ^ k := by
  have h := power_decay_bound_with_clock g g' (fun t ↦ t / Real.exp 1)
    (fun _ ↦ 1 / Real.exp 1) a k ha hk hgcont
    (continuous_id.div_const _).continuousOn hgnonneg
    (fun _ _ ↦ by positivity) hgderiv
    (fun t _ ↦ (hasDerivAt_id t).div_const (Real.exp 1))
    (fun t ht ↦ by simpa only [div_eq_mul_inv, one_mul] using hode t ht)
    (by simp only [zero_div, sub_zero]; positivity)
  simpa only [zero_div, sub_zero, inv_div] using h


end PrescribedDecay
lemma l53_condLaw_probability {V : Type*} [Fintype V] [LinearOrder V]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (rA : V → ℝ) :
    IsProbabilityMeasure (condLaw r₀ θ A rA) := by
  have : IsProbabilityMeasure (expMeasure (1:ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have : IsProbabilityMeasure ((expMeasure (1:ℝ)).map (fun x => θ+x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold condLaw
  have : ∀ v : V, IsProbabilityMeasure
      (if r₀ v < θ then Measure.dirac (r₀ v)
       else if v ∈ A then Measure.dirac (rA v) else (expMeasure 1).map (fun x => θ+x)) := by
    intro v
    split_ifs <;> infer_instance
  infer_instance



lemma Ncount_zero_le_one {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (t : ℝ) (r : V → ℝ) :
    Ncount G A 0 t r ≤ 1 := by
  classical
  unfold Ncount
  have hsub : (Finset.univ.filter (fun W : Finset V => W.card = 0 ∧
      IsAttached G A W ∧ ActiveAt G r t (A ∪ W))) ⊆ {∅} := by
    intro W hW
    exact Finset.mem_singleton.mpr (Finset.card_eq_zero.mp (Finset.mem_filter.mp hW).2.1)
  simpa using Finset.card_le_card hsub

lemma Ncount_zero_integral {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (t θ : ℝ)
    (r₀ rA : V → ℝ) :
    ∫⁻ r, (Ncount G A 0 t r : ℝ≥0∞) ∂(condLaw r₀ θ A rA) ≤ 1 := by
  have := l53_condLaw_probability r₀ θ A rA
  calc
    _ ≤ ∫⁻ r : V → ℝ, (1:ℝ≥0∞) ∂(condLaw r₀ θ A rA) := by
      apply lintegral_mono
      intro r
      change (Ncount G A 0 t r : ℝ≥0∞) ≤ 1
      exact_mod_cast Ncount_zero_le_one G A t r
    _ = 1 := by simp

theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ a : ℝ) (hθ : 0 ≤ θ) (hθa : θ < a) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ θ) (A : Finset V) (hA : IsConnectedSet G A)
    (hAθ : ActiveAt G r₀ θ A) (rA : V → ℝ) (hrA : ∀ v ∈ A, a ≤ rA v) (k : ℕ) :
    Measurable (fun r : V → ℝ => Ncount G A k a r) ∧
    ∫⁻ r, (Ncount G A k a r : ℝ≥0∞) ∂(condLaw r₀ θ A rA) ≤
      ENNReal.ofReal ((Real.exp 1 / (a - θ)) ^ k) := by
  refine ⟨Ncount_measurable G A k a, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using Ncount_zero_integral G A a θ r₀ rA
  · obtain ⟨f,f',hrep,hcont,hnonneg,hderiv,hode⟩ :=
      prescribed_extension_drift G θ a hθ hθa r₀ hr₀ A hA hAθ rA hrA k hk
    have hb := PrescribedDecay.power_decay_bound f f' (a-θ) k (sub_pos.mpr hθa) hk
      hcont hnonneg hderiv hode
    have he := hrep (a-θ) ⟨(sub_pos.mpr hθa).le, le_rfl⟩
    rw [show θ+(a-θ) = a by ring] at he
    rw [he]
    exact ENNReal.ofReal_le_ofReal hb


