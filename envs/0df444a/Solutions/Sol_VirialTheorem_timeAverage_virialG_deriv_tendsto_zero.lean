-- Prove2me | solution 1 for VirialTheorem.timeAverage_virialG_deriv_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:14:22.757163+00:00
-- url     : https://prove2.me/submissions/9c27c0a9-6cde-450e-8e32-660e2912ef76

import Definitions.Def_virial_theorem_defs

set_option autoImplicit false
open VirialTheorem Filter Topology

private theorem virial_derivative {N : ℕ} (m : Fin N → ℝ)
    (r v F : Fin N → ℝ → Space) (t : ℝ)
    (hr : ∀ k, HasDerivAt (r k) (v k t) t)
    (hp : ∀ k, HasDerivAt (fun s => m k • v k s) (F k t) t) :
    HasDerivAt (virialG m r v)
      (2 * kineticEnergy m v t + ∑ k, inner ℝ (F k t) (r k t)) t := by
  change HasDerivAt (fun s => ∑ k, inner ℝ (m k • v k s) (r k s)) _ t
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun k _ => (hp k).inner ℝ (hr k))
  simpa [virialG, kineticEnergy, real_inner_smul_left, real_inner_self_eq_norm_sq,
    Finset.sum_add_distrib] using hsum

private theorem average_identity {N : ℕ} (m : Fin N → ℝ) (r v F : Fin N → ℝ → Space)
    (hr : ∀ k t, HasDerivAt (r k) (v k t) t)
    (hp : ∀ k t, HasDerivAt (fun s => m k • v k s) (F k t) t)
    (hF : ∀ k, Continuous (F k))
    (τ : ℝ) (hτ : 0 < τ) :
    timeAverage (deriv (virialG m r v)) τ = (virialG m r v τ - virialG m r v 0) / τ ∧
    timeAverage (deriv (virialG m r v)) τ =
      2 * timeAverage (kineticEnergy m v) τ +
        ∑ k, timeAverage (fun t => inner ℝ (F k t) (r k t)) τ := by
  have hcR (k : Fin N) : Continuous (r k) :=
    continuous_iff_continuousAt.mpr (fun t => (hr k t).continuousAt)
  have hcP (k : Fin N) : Continuous (fun t => m k • v k t) :=
    continuous_iff_continuousAt.mpr (fun t => (hp k t).continuousAt)
  have hcV (k : Fin N) (hm : m k ≠ 0) : Continuous (v k) := by
    have hc : Continuous (fun t => (m k)⁻¹ • (m k • v k t)) := (hcP k).const_smul (m k)⁻¹
    simpa [smul_smul, hm] using hc
  have hcK : Continuous (kineticEnergy m v) := by
    unfold kineticEnergy
    apply Continuous.const_mul
    apply continuous_finset_sum
    intro k _
    by_cases hm : m k = 0
    · simp only [hm, zero_mul]
      exact continuous_const
    · exact ((hcV k hm).norm.pow 2).const_mul (m k)
  have hcW (k : Fin N) : Continuous (fun t => inner ℝ (F k t) (r k t)) :=
    (hF k).inner (hcR k)
  have hcS : Continuous (fun t => ∑ k, inner ℝ (F k t) (r k t)) :=
    continuous_finset_sum _ (fun k _ => hcW k)
  have heq : deriv (virialG m r v) =
      fun t => 2 * kineticEnergy m v t + ∑ k, inner ℝ (F k t) (r k t) := by
    funext t
    exact (virial_derivative m r v F t (fun k => hr k t) (fun k => hp k t)).deriv
  have hcd : Continuous (deriv (virialG m r v)) := by
    rw [heq]
    exact (hcK.const_mul 2).add hcS
  constructor
  · unfold timeAverage
    rw [heq, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => virial_derivative m r v F t (fun k => hr k t) (fun k => hp k t))
      ((hcK.const_mul 2).add hcS |>.intervalIntegrable 0 τ)]
    simp only [div_eq_mul_inv, mul_comm]
  · unfold timeAverage
    rw [heq, intervalIntegral.integral_add ((hcK.const_mul 2).intervalIntegrable 0 τ)
      (hcS.intervalIntegrable 0 τ), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun k _ => (hcW k).intervalIntegrable 0 τ)]
    rw [mul_add, Finset.mul_sum]
    ring

private theorem bounded_quotient_zero (f : ℝ → ℝ) (C : ℝ)
    (h : ∀ t ≥ 0, |f t| ≤ C) :
    Tendsto (fun t => (f t - f 0) / t) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => (2 * C) / t) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul (2 * C))
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht]
  apply div_le_div_of_nonneg_right _ ht.le
  calc
    |f t - f 0| ≤ |f t| + |f 0| := abs_sub _ _
    _ ≤ C + C := add_le_add (h t ht.le) (h 0 le_rfl)
    _ = 2 * C := by ring

private theorem virial_bounded {N : ℕ} (m : Fin N → ℝ) (r v : Fin N → ℝ → Space)
    (hbdd : ∃ C : ℝ, ∀ t ≥ 0, ∀ k, ‖r k t‖ ≤ C ∧ ‖v k t‖ ≤ C) :
    ∃ B : ℝ, ∀ t ≥ 0, |virialG m r v t| ≤ B := by
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨∑ k, |m k| * |C| ^ 2, ?_⟩
  intro t ht
  unfold virialG
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  calc
    |inner ℝ (m k • v k t) (r k t)| ≤ ‖m k • v k t‖ * ‖r k t‖ :=
      abs_real_inner_le_norm _ _
    _ = |m k| * ‖v k t‖ * ‖r k t‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |m k| * |C| * |C| := by
      gcongr
      · exact (hC t ht k).2.trans (le_abs_self C)
      · exact (hC t ht k).1.trans (le_abs_self C)
    _ = |m k| * |C| ^ 2 := by ring

theorem solution {N : ℕ} (m : Fin N → ℝ)
    (r v F : Fin N → ℝ → Space)
    (hr : ∀ k t, HasDerivAt (r k) (v k t) t)
    (hp : ∀ k t, HasDerivAt (fun s => m k • v k s) (F k t) t)
    (hF : ∀ k, Continuous (F k))
    (hbdd : ∃ C : ℝ, ∀ t ≥ 0, ∀ k, ‖r k t‖ ≤ C ∧ ‖v k t‖ ≤ C) :
    Tendsto (fun τ => timeAverage (deriv (virialG m r v)) τ) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := virial_bounded m r v hbdd
  apply (bounded_quotient_zero (virialG m r v) B hB).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  exact (average_identity m r v F hr hp hF τ hτ).1.symm
