-- Prove2me | solution 1 for RobbinsMonroSA.Conv.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-26T05:15:38.603635+00:00
-- url     : https://prove2.me/submissions/736c0992-03bd-4e5c-a355-099fb41e457e

-- SPDX-License-Identifier: Apache-2.0

import Definitions.Def_RobbinsMonroSA_Conv_Setting


section

open MeasureTheory ProbabilityTheory Filter Topology
namespace RobbinsMonroSA.Conv.RMFresh

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {H : Kernel ℝ ℝ} [IsMarkovKernel H] {C α θ x1 : ℝ} {a : ℕ → ℝ}
  {x y : ℕ → Ω → ℝ}

theorem response_bound (h4 : BoundedResponse H C) (z : ℝ) :
    ∀ᵐ t ∂H z, |t| ≤ C := by
  have h : Set.Icc (-C) C ∈ ae (H z) :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 (h4.2 z)
  filter_upwards [h] with t ht
  exact abs_le.mpr ht

theorem response_integrable (h4 : BoundedResponse H C) (z : ℝ) :
    Integrable (fun t : ℝ => t) (H z) := by
  exact Integrable.of_bound measurable_id.aestronglyMeasurable C
    (by simpa only [Real.norm_eq_abs] using response_bound h4 z)

theorem regression_bound (h4 : BoundedResponse H C) (z : ℝ) :
    |regressionFn H z| ≤ C := by
  simpa [regressionFn, Real.norm_eq_abs] using
    norm_integral_le_of_norm_le_const (by simpa only [Real.norm_eq_abs] using response_bound h4 z : ∀ᵐ t ∂H z, ‖t‖ ≤ C)

theorem regression_measurable : Measurable (regressionFn H) := by
  exact (measurable_snd.stronglyMeasurable.integral_kernel_prod_right' (κ := H)).measurable

omit [IsProbabilityMeasure P] in
theorem process_response_bound (h4 : BoundedResponse H C)
    (hxy : IsRMProcess P H a α x1 x y) (n : ℕ) :
    ∀ᵐ ω ∂P, |y n ω| ≤ C := by
  have h : ∀ᵐ p : ℝ × ℝ ∂((P.map (x n)) ⊗ₘ H), |p.2| ≤ C := by
    apply Measure.ae_compProd_of_ae_ae (measurableSet_le measurable_snd.abs measurable_const)
    exact Eventually.of_forall (fun z => response_bound h4 z)
  rw [← hxy.law n] at h
  exact ae_of_ae_map ((hxy.measurable_x n).prodMk (hxy.measurable_y n)).aemeasurable h

theorem bigA_nonnegative (hC : 0 ≤ C) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    0 ≤ bigA x1 θ C α a n := by
  unfold bigA
  exact add_nonneg (abs_nonneg _) (mul_nonneg (add_nonneg hC (abs_nonneg _))
    (Finset.sum_nonneg fun i _ => ha i))

omit [IsProbabilityMeasure P] in
theorem process_state_bound (h4 : BoundedResponse H C)
    (hxy : IsRMProcess P H a α x1 x y) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    ∀ᵐ ω ∂P, |x n ω - θ| ≤ bigA x1 θ C α a n := by
  induction n with
  | zero => simp [hxy.init, bigA]
  | succ n ih =>
    filter_upwards [ih, process_response_bound h4 hxy n] with ω hx hy
    have hstep : x (n+1) ω - θ = (x n ω - θ) + a n * (α - y n ω) := by
      linarith [hxy.step n ω]
    have hinc : |α - y n ω| ≤ C + |α| := by
      calc
        |α - y n ω| ≤ |α| + |y n ω| := abs_sub _ _
        _ ≤ C + |α| := by linarith
    calc
      |x (n+1) ω - θ| ≤ |x n ω - θ| + a n * |α - y n ω| := by
        rw [hstep]; simpa [abs_mul, abs_of_nonneg (ha n)] using
          (abs_add_le (x n ω - θ) (a n * (α - y n ω)))
      _ ≤ bigA x1 θ C α a n + a n * (C + |α|) :=
        add_le_add hx (mul_le_mul_of_nonneg_left hinc (ha n))
      _ = bigA x1 θ C α a (n+1) := by unfold bigA; rw [Finset.sum_range_succ]; ring

theorem state_square_integrable (h4 : BoundedResponse H C)
    (hxy : IsRMProcess P H a α x1 x y) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    Integrable (fun ω => (x n ω - θ)^2) P := by
  apply Integrable.of_bound (((hxy.measurable_x n).sub measurable_const).pow_const 2).aestronglyMeasurable
    ((bigA x1 θ C α a n)^2)
  filter_upwards [process_state_bound (θ := θ) h4 hxy ha n] with ω hω
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hω 2

theorem drift_integrable (h4 : BoundedResponse H C)
    (hxy : IsRMProcess P H a α x1 x y) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    Integrable (fun ω => (x n ω - θ) * (regressionFn H (x n ω) - α)) P := by
  apply Integrable.of_bound
    (((hxy.measurable_x n).sub measurable_const).mul
      ((regression_measurable.comp (hxy.measurable_x n)).sub measurable_const)).aestronglyMeasurable
    (bigA x1 θ C α a n * (C + |α|))
  filter_upwards [process_state_bound (θ := θ) h4 hxy ha n] with ω hω
  change |(x n ω - θ) * (regressionFn H (x n ω) - α)| ≤ _
  rw [abs_mul]
  apply mul_le_mul hω _ (abs_nonneg _) (bigA_nonnegative h4.1.le ha n)
  have hb := regression_bound h4 (x n ω)
  have ht := abs_sub (regressionFn H (x n ω)) α
  linarith

omit [IsProbabilityMeasure P] in
theorem msd_nonnegative (n : ℕ) : 0 ≤ msd P x θ n := by
  exact integral_nonneg fun _ => sq_nonneg _

omit [IsProbabilityMeasure P] [IsMarkovKernel H] in
theorem drift_nonnegative (hmono : Monotone (regressionFn H))
    (hroot : regressionFn H θ = α) (n : ℕ) : 0 ≤ dSeq P H α θ x n := by
  apply integral_nonneg
  intro ω
  rcases le_total θ (x n ω) with h | h
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (hroot ▸ hmono h))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
      (sub_nonpos.mpr (hroot ▸ hmono h))

end RobbinsMonroSA.Conv.RMFresh
end


section

open MeasureTheory ProbabilityTheory Filter Topology
namespace RobbinsMonroSA.Conv.RMFresh

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {H : Kernel ℝ ℝ} [IsMarkovKernel H] {C α θ x1 : ℝ} {a : ℕ → ℝ}
  {x y : ℕ → Ω → ℝ}

theorem joint_integral_transfer (hxy : IsRMProcess P H a α x1 x y) (n : ℕ)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun ω => f (x n ω, y n ω)) P) :
    (∫ ω, f (x n ω, y n ω) ∂P) = ∫ ω, ∫ t, f (x n ω, t) ∂H (x n ω) ∂P := by
  have hp := (hxy.measurable_x n).prodMk (hxy.measurable_y n)
  have hj : Integrable f (P.map (fun ω => (x n ω, y n ω))) :=
    (integrable_map_measure hf.aestronglyMeasurable hp.aemeasurable).2 hi
  have ht := integral_map (μ := P) hp.aemeasurable hf.aestronglyMeasurable
  rw [hxy.law n] at hj ht
  rw [Measure.integral_compProd hj] at ht
  have hm : Measurable (fun z => ∫ t, f (z,t) ∂H z) :=
    hf.stronglyMeasurable.integral_kernel_prod_right'.measurable
  exact ht.symm.trans (integral_map (hxy.measurable_x n).aemeasurable hm.aestronglyMeasurable)

theorem response_error_integrable (h4 : BoundedResponse H C)
    (hxy : IsRMProcess P H a α x1 x y) (n : ℕ) :
    Integrable (fun ω => (y n ω - α)^2) P := by
  apply Integrable.of_bound (((hxy.measurable_y n).sub measurable_const).pow_const 2).aestronglyMeasurable
    ((C + |α|)^2)
  filter_upwards [process_response_bound h4 hxy n] with ω hω
  change |(y n ω - α)^2| ≤ _
  rw [abs_pow]
  apply pow_le_pow_left₀ (abs_nonneg _) _ 2
  exact (abs_sub _ _).trans (by linarith)

theorem cross_error_integrable (h4 : BoundedResponse H C)
    (hxy : IsRMProcess P H a α x1 x y) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    Integrable (fun ω => (x n ω - θ) * (y n ω - α)) P := by
  apply Integrable.of_bound
    (((hxy.measurable_x n).sub measurable_const).mul
      ((hxy.measurable_y n).sub measurable_const)).aestronglyMeasurable
    (bigA x1 θ C α a n * (C + |α|))
  filter_upwards [process_state_bound (θ := θ) h4 hxy ha n, process_response_bound h4 hxy n] with ω hx hy
  change |(x n ω - θ) * (y n ω - α)| ≤ _
  rw [abs_mul]
  apply mul_le_mul hx _ (abs_nonneg _) (bigA_nonnegative h4.1.le ha n)
  exact (abs_sub _ _).trans (by linarith)

theorem eSeq_eq_response (h4 : BoundedResponse H C)
    (hxy : IsRMProcess P H a α x1 x y) (n : ℕ) :
    eSeq P H α x n = ∫ ω, (y n ω - α)^2 ∂P := by
  exact (joint_integral_transfer hxy n (fun p => (p.2-α)^2)
    (by fun_prop) (response_error_integrable h4 hxy n)).symm

theorem dSeq_eq_cross (h4 : BoundedResponse H C)
    (hxy : IsRMProcess P H a α x1 x y) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    dSeq P H α θ x n = ∫ ω, (x n ω - θ) * (y n ω - α) ∂P := by
  rw [joint_integral_transfer hxy n (fun p => (p.1-θ)*(p.2-α)) (by fun_prop)
    (cross_error_integrable h4 hxy ha n)]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    dsimp only
    rw [integral_const_mul, integral_sub (response_integrable h4 _) (integrable_const α)]
    simp [regressionFn]

theorem eSeq_bounds (h4 : BoundedResponse H C)
    (hxy : IsRMProcess P H a α x1 x y) (n : ℕ) :
    0 ≤ eSeq P H α x n ∧ eSeq P H α x n ≤ (C + |α|)^2 := by
  rw [eSeq_eq_response h4 hxy n]
  constructor
  · exact integral_nonneg fun _ => sq_nonneg _
  · calc
      (∫ ω, (y n ω - α)^2 ∂P) ≤ ∫ _ : Ω, (C + |α|)^2 ∂P := by
        apply integral_mono_ae (response_error_integrable h4 hxy n) (integrable_const _)
        filter_upwards [process_response_bound h4 hxy n] with ω hy
        have hb : |y n ω - α| ≤ C + |α| := (abs_sub _ _).trans (by linarith)
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = (C + |α|)^2 := by simp

theorem native_energy_recurrence (h4 : BoundedResponse H C)
    (hxy : IsRMProcess P H a α x1 x y) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    msd P x θ (n+1) - msd P x θ n = a n^2 * eSeq P H α x n - 2 * a n * dSeq P H α θ x n := by
  have hb := state_square_integrable (θ := θ) h4 hxy ha n
  have he := response_error_integrable h4 hxy n
  have hd := cross_error_integrable (θ := θ) h4 hxy ha n
  have hi : (∫ ω, (x (n+1) ω - θ)^2 ∂P) =
      (∫ ω, (x n ω - θ)^2 + a n^2 * (y n ω - α)^2 -
        (2*a n) * ((x n ω - θ)*(y n ω - α)) ∂P) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      have hs := hxy.step n ω
      have hx : x (n+1) ω - θ = (x n ω-θ) - a n*(y n ω-α) := by linarith
      dsimp only
      rw [hx]; ring
  have hsub := integral_sub (hb.add (he.const_mul (a n^2))) (hd.const_mul (2*a n))
  have hadd := integral_add hb (he.const_mul (a n^2))
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub, hadd, integral_const_mul, integral_const_mul] at hi
  rw [eSeq_eq_response h4 hxy n, dSeq_eq_cross h4 hxy ha n]
  unfold msd
  linarith

end RobbinsMonroSA.Conv.RMFresh
end


section

namespace RobbinsMonroSA.Conv.RMFresh
open Filter Topology

theorem positive_derivative_local_secant {M : ℝ → ℝ} {θ r : ℝ}
    (hderiv : HasDerivAt M r θ) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≠ θ → |z-θ| ≤ δ →
      r/2 ≤ (M z-M θ)/(z-θ) := by
  classical
  have he : ∀ᶠ z in 𝓝 θ,
      r/2 < Function.update (fun z => (M z-M θ)/(z-θ)) θ r z := by
    apply hderiv.continuousAt_div.eventually
    simpa using (lt_mem_nhds (show r/2 < r by linarith))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε/2, by positivity, ?_⟩
  intro z hz hdist
  have hzdist : dist z θ < ε := by rw [Real.dist_eq]; linarith
  have h := he hzdist
  simpa [Function.update_of_ne hz] using h.le

theorem monotone_local_secant_global {M : ℝ → ℝ} {θ α δ r : ℝ}
    (hmono : Monotone M) (hδ : 0 < δ) (hr : 0 < r)
    (hlocal : ∀ z : ℝ, z ≠ θ → |z-θ| ≤ δ → r ≤ (M z-α)/(z-θ))
    (A : ℝ) (hA : δ ≤ A) (z : ℝ) (hzA : |z-θ| ≤ A) :
    (δ*r/A)*(z-θ)^2 ≤ (z-θ)*(M z-α) := by
  have hAp : 0 < A := hδ.trans_le hA
  by_cases hz : z = θ
  · subst z
    simp
  have hsq : 0 ≤ (z-θ)^2 := sq_nonneg _
  have hsec : δ*r/A ≤ (M z-α)/(z-θ) := by
    by_cases hnear : |z-θ| ≤ δ
    · apply le_trans _ (hlocal z hz hnear)
      apply (div_le_iff₀ hAp).2
      nlinarith
    · have hfar : δ < |z-θ| := lt_of_not_ge hnear
      by_cases hp : θ < z
      · have hu : 0 < z-θ := sub_pos.mpr hp
        have hup : z-θ ≤ A := (le_abs_self _).trans hzA
        have hδu : δ < z-θ := by simpa [abs_of_pos hu] using hfar
        have he := hlocal (θ+δ) (by linarith) (by simp [abs_of_pos hδ])
        have he' : r*δ ≤ M (θ+δ)-α := by
          have := (le_div_iff₀ hδ).mp (by simpa using he)
          exact this
        have hm := hmono (show θ+δ ≤ z by linarith)
        calc
          δ*r/A ≤ δ*r/(z-θ) := div_le_div_of_nonneg_left (by positivity) hu hup
          _ ≤ (M z-α)/(z-θ) := div_le_div_of_nonneg_right (by nlinarith) hu.le
      · have hu : 0 < θ-z := by have := lt_of_le_of_ne (le_of_not_gt hp) hz; linarith
        have hup : θ-z ≤ A := by simpa [abs_of_neg (by linarith : z-θ < 0)] using hzA
        have hδu : δ < θ-z := by simpa [abs_of_neg (by linarith : z-θ < 0)] using hfar
        have he := hlocal (θ-δ) (by linarith) (by simp [abs_of_pos hδ])
        have he' : r*δ ≤ α-M (θ-δ) := by
          have hn : θ-δ-θ < 0 := by linarith
          have ht := (le_div_iff_of_neg hn).mp he
          nlinarith
        have hm := hmono (show z ≤ θ-δ by linarith)
        calc
          δ*r/A ≤ δ*r/(θ-z) := div_le_div_of_nonneg_left (by positivity) hu hup
          _ ≤ (α-M z)/(θ-z) := div_le_div_of_nonneg_right (by nlinarith) hu.le
          _ = (M z-α)/(z-θ) := by simpa only [neg_sub] using (neg_div_neg_eq (M z-α) (z-θ))
  have h := mul_le_mul_of_nonneg_right hsec hsq
  have hne : z-θ ≠ 0 := sub_ne_zero.mpr hz
  have heq : ((M z-α)/(z-θ))*(z-θ)^2 = (z-θ)*(M z-α) := by
    field_simp
  rwa [heq] at h

theorem positive_derivative_growing_coercivity {M : ℝ → ℝ} {θ α r : ℝ}
    (hmono : Monotone M) (hcenter : M θ = α) (hderiv : HasDerivAt M r θ) (hr : 0 < r) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ A : ℝ, δ ≤ A → ∀ z : ℝ,
      |z-θ| ≤ A → (K/A)*(z-θ)^2 ≤ (z-θ)*(M z-α) := by
  obtain ⟨δ,hδ,hlocal⟩ := positive_derivative_local_secant hderiv hr
  refine ⟨δ,δ*(r/2),hδ,by positivity,?_⟩
  intro A hA z hz
  apply monotone_local_secant_global hmono hδ (by linarith : 0 < r/2)
    (fun z hz hzd => ?_) A hA z hz
  simpa [hcenter] using hlocal z hz hzd

end RobbinsMonroSA.Conv.RMFresh
end


section

namespace RobbinsMonroSA.Conv.RMFresh
open Filter Topology
open scoped BigOperators

def stepSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, a i

theorem stepSum_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (n : ℕ) :
    0 ≤ stepSum a n := Finset.sum_nonneg fun i _ => (ha i).le

theorem stepSum_mono {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) : Monotone (stepSum a) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [stepSum, Finset.sum_range_succ]
  linarith [ha n]

theorem stepSum_succ_pos {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (n : ℕ) :
    0 < stepSum a (n+1) := by
  have h := stepSum_mono ha (show 1 ≤ n+1 by omega)
  have h0 : a 0 ≤ stepSum a (n+1) := by simpa [stepSum] using h
  exact (ha 0).trans_le h0

theorem ratio_partial_sum_bound {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (N : ℕ) :
    (∑ n ∈ Finset.range N, a (n+1) / stepSum a (n+1)) ≤ stepSum a (N+1) / a 0 := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, a (n+1) / a 0 := by
      apply Finset.sum_le_sum
      intro n _
      apply div_le_div_of_nonneg_left (ha (n+1)).le (ha 0)
      have h := stepSum_mono ha (show 1 ≤ n+1 by omega)
      simpa [stepSum] using h
    _ = (∑ n ∈ Finset.range N, a (n+1)) / a 0 := by rw [Finset.sum_div]
    _ ≤ stepSum a (N+1) / a 0 := by
      apply div_le_div_of_nonneg_right _ (ha 0).le
      rw [stepSum, Finset.sum_range_succ']
      linarith [ha 0]

theorem stepSum_tendsto_atTop {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (h26 : StepCond26 a) : Tendsto (stepSum a) atTop atTop := by
  apply (stepSum_mono ha).tendsto_atTop_atTop
  intro b
  have hq : ∀ᶠ N in atTop,
      b / a 0 ≤ ∑ n ∈ Finset.range N, a (n+1) / stepSum a (n+1) :=
    h26.eventually (eventually_ge_atTop (b / a 0))
  obtain ⟨N, hN⟩ := hq.exists
  refine ⟨N+1, ?_⟩
  exact (div_le_div_iff_of_pos_right (ha 0)).mp (hN.trans (ratio_partial_sum_bound ha N))

theorem bigA_eventually_le_twice_steps {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (h26 : StepCond26 a) (x1 θ C α : ℝ) (hC : 0 < C) :
    ∀ᶠ n in atTop, 0 < bigA x1 θ C α a n ∧
      bigA x1 θ C α a n ≤ 2*(C+|α|)*stepSum a n := by
  have hD : 0 < C+|α| := by positivity
  have hS := stepSum_tendsto_atTop ha h26
  filter_upwards [hS.eventually (eventually_ge_atTop (|x1-θ|/(C+|α|))),
    hS.eventually (eventually_ge_atTop 1)] with n hn hn1
  have hbound := (div_le_iff₀ hD).mp hn
  change 0 < |x1-θ|+(C+|α|)*stepSum a n ∧ _
  constructor
  · positivity
  · change |x1-θ|+(C+|α|)*stepSum a n ≤ _
    nlinarith

theorem bigA_tendsto_atTop {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (h26 : StepCond26 a) (x1 θ C α : ℝ) (hC : 0 < C) :
    Tendsto (bigA x1 θ C α a) atTop atTop := by
  have hD : 0 < C+|α| := by positivity
  have ht := (stepSum_tendsto_atTop ha h26).const_mul_atTop hD
  change Tendsto (fun n => |x1-θ|+(C+|α|)*stepSum a n) atTop atTop
  exact tendsto_const_nhds.add_atTop ht

end RobbinsMonroSA.Conv.RMFresh
end


section

open MeasureTheory ProbabilityTheory Filter Topology
namespace RobbinsMonroSA.Conv.RMFresh

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {H : Kernel ℝ ℝ} [IsMarkovKernel H] {C α θ x1 : ℝ} {a : ℕ → ℝ}
  {x y : ℕ → Ω → ℝ}

theorem native_drift_lower_bound (h4 : BoundedResponse H C)
    (hxy : IsRMProcess P H a α x1 x y) (ha : ∀ n, 0 ≤ a n)
    (K : ℝ) (n : ℕ)
    (hpoint : ∀ z : ℝ, |z-θ| ≤ bigA x1 θ C α a n →
      (K / bigA x1 θ C α a n)*(z-θ)^2 ≤ (z-θ)*(regressionFn H z-α)) :
    (K / bigA x1 θ C α a n)*msd P x θ n ≤ dSeq P H α θ x n := by
  rw [msd, dSeq, ← integral_const_mul]
  apply integral_mono_ae ((state_square_integrable h4 hxy ha n).const_mul _)
    (drift_integrable h4 hxy ha n)
  filter_upwards [process_state_bound (θ := θ) h4 hxy ha n] with ω hω
  exact hpoint (x n ω) hω

theorem native_drift_eventual (h4 : BoundedResponse H C)
    (hxy : IsRMProcess P H a α x1 x y) (ha : IsTypeOneOverN a)
    (hmono : Monotone (regressionFn H)) (hroot : regressionFn H θ = α)
    (r : ℝ) (hderiv : HasDerivAt (regressionFn H) r θ) (hr : 0 < r) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
      (K / bigA x1 θ C α a n)*msd P x θ n ≤ dSeq P H α θ x n := by
  obtain ⟨δ,K,hδ,hK,hpoint⟩ := positive_derivative_growing_coercivity hmono hroot hderiv hr
  refine ⟨K,hK,?_⟩
  have hA := bigA_tendsto_atTop ha.1.1 ha.2 x1 θ C α h4.1
  filter_upwards [hA.eventually (eventually_ge_atTop δ)] with n hn
  exact native_drift_lower_bound h4 hxy (fun i => (ha.1.1 i).le) K n (hpoint _ hn)

end RobbinsMonroSA.Conv.RMFresh
end


section

namespace RobbinsMonroSA.Conv.RMFresh
open Filter Topology
open scoped BigOperators

theorem energy_telescope (b u v : ℕ → ℝ)
    (hrec : ∀ n, b (n+1)-b n = u n-2*v n) (N : ℕ) :
    b N + 2*(∑ i ∈ Finset.range N, v i) = b 0 + ∑ i ∈ Finset.range N, u i := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    linarith [hrec N]

theorem energy_summable_limit (b u v : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (hsu : Summable u) (hrec : ∀ n, b (n+1)-b n = u n-2*v n) :
    Summable v ∧ ∃ L : ℝ, 0 ≤ L ∧ Tendsto b atTop (𝓝 L) := by
  have hsumv : Summable v := summable_of_sum_range_le hv (fun N => by
    have htel := energy_telescope b u v hrec N
    have hup := hsu.sum_le_tsum (Finset.range N) (fun i _ => hu i)
    have hbN := hb N
    show (∑ i ∈ Finset.range N, v i) ≤ (b 0+∑' i, u i)/2
    linarith)
  have heq : b = fun N => b 0+(∑ i ∈ Finset.range N, u i)-2*(∑ i ∈ Finset.range N, v i) := by
    funext N
    linarith [energy_telescope b u v hrec N]
  have hlim : Tendsto b atTop (𝓝 (b 0+(∑' i, u i)-2*(∑' i, v i))) := by
    have ht : Tendsto (fun N => b 0+(∑ i ∈ Finset.range N, u i)-2*(∑ i ∈ Finset.range N, v i))
        atTop (𝓝 (b 0+(∑' i, u i)-2*(∑' i, v i))) :=
      (tendsto_const_nhds.add hsu.hasSum.tendsto_sum_nat).sub
        (tendsto_const_nhds.mul hsumv.hasSum.tendsto_sum_nat)
    exact ht.congr (fun N => (congrFun heq N).symm)
  exact ⟨hsumv, _, ge_of_tendsto hlim (Filter.Eventually.of_forall hb), hlim⟩

theorem rm_energy_summable_limit (a b d e : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hsa : Summable (fun n => a n^2))
    (hb : ∀ n, 0 ≤ b n) (hd : ∀ n, 0 ≤ d n)
    (E : ℝ) (he : ∀ n, 0 ≤ e n ∧ e n ≤ E)
    (hrec : ∀ n, b (n+1)-b n = a n^2*e n-2*a n*d n) :
    Summable (fun n => a n*d n) ∧ ∃ L : ℝ, 0 ≤ L ∧ Tendsto b atTop (𝓝 L) := by
  have hsu : Summable (fun n => a n^2*e n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (he n).1)
      (fun n => mul_le_mul_of_nonneg_left (he n).2 (sq_nonneg _)) (hsa.mul_right E)
  apply energy_summable_limit b (fun n => a n^2*e n) (fun n => a n*d n)
    hb (fun n => mul_nonneg (sq_nonneg _) (he n).1)
    (fun n => mul_nonneg (ha n).le (hd n)) hsu
  intro n
  nlinarith [hrec n]

end RobbinsMonroSA.Conv.RMFresh
end


section

namespace RobbinsMonroSA.Conv.RMFresh
open Filter Topology

theorem step_ratios_not_summable {a : ℕ → ℝ} (h26 : StepCond26 a) :
    ¬ Summable (fun n => a (n+1)/stepSum a (n+1)) := by
  intro hs
  exact not_tendsto_atTop_of_tendsto_nhds hs.hasSum.tendsto_sum_nat h26

theorem drift_limit_zero (a b d : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h26 : StepCond26 a) (hd : ∀ n, 0 ≤ d n)
    (hs : Summable (fun n => a n*d n)) (L : ℝ) (hL : 0 ≤ L)
    (hb : Tendsto b atTop (𝓝 L)) (x1 θ C α : ℝ) (hC : 0 < C)
    (K : ℝ) (hK : 0 < K)
    (hdrift : ∀ᶠ n in atTop, (K/bigA x1 θ C α a n)*b n ≤ d n) : L = 0 := by
  by_contra hne
  have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hne)
  let D : ℝ := C+|α|
  have hD : 0 < D := by dsimp [D]; positivity
  let c : ℝ := K*L/(4*D)
  have hc : 0 < c := by dsimp [c]; positivity
  have hbpos : ∀ᶠ n in atTop, L/2 ≤ b n :=
    (hb.eventually (lt_mem_nhds (show L/2 < L by linarith))).mono fun _ h => h.le
  have hcoeff : ∀ᶠ n in atTop, c ≤ d n*stepSum a n := by
    filter_upwards [hdrift,hbpos,bigA_eventually_le_twice_steps ha h26 x1 θ C α hC] with n hn hbn hAn
    have hmul : K*b n ≤ d n*bigA x1 θ C α a n := by
      apply (div_le_iff₀ hAn.1).mp
      simpa [div_mul_eq_mul_div] using hn
    have hup := mul_le_mul_of_nonneg_left hAn.2 (hd n)
    change K*L/(4*D) ≤ _
    apply (div_le_iff₀ (show 0 < 4*D by positivity)).2
    change d n*bigA x1 θ C α a n ≤ d n*(2*D*stepSum a n) at hup
    nlinarith
  have hshift : Summable (fun n => a (n+1)*d (n+1)/c) :=
    (hs.comp_injective (fun m n h => by omega)).div_const c
  have hqs : Summable (fun n => a (n+1)/stepSum a (n+1)) := by
    apply Summable.of_norm_bounded_eventually_nat hshift
    have hcshift := (tendsto_add_atTop_nat 1).eventually hcoeff
    filter_upwards [hcshift] with n hn
    have hS := stepSum_succ_pos ha n
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (ha _) hS)]
    apply (le_div_iff₀ hc).2
    have hdiv : c/stepSum a (n+1) ≤ d (n+1) := (div_le_iff₀ hS).2 hn
    have hmul := mul_le_mul_of_nonneg_left hdiv (ha (n+1)).le
    convert hmul using 1
    ring
  exact step_ratios_not_summable h26 hqs

theorem rm_energy_drift_converges_zero (a b d e : ℕ → ℝ)
    (ha : IsTypeOneOverN a) (hb : ∀ n, 0 ≤ b n) (hd : ∀ n, 0 ≤ d n)
    (E : ℝ) (he : ∀ n, 0 ≤ e n ∧ e n ≤ E)
    (hrec : ∀ n, b (n+1)-b n = a n^2*e n-2*a n*d n)
    (x1 θ C α : ℝ) (hC : 0 < C) (K : ℝ) (hK : 0 < K)
    (hdrift : ∀ᶠ n in atTop, (K/bigA x1 θ C α a n)*b n ≤ d n) :
    Tendsto b atTop (𝓝 0) := by
  obtain ⟨hs,L,hL,hlim⟩ := rm_energy_summable_limit a b d e ha.1.1 ha.1.2 hb hd E he hrec
  have hzero := drift_limit_zero a b d ha.1.1 ha.2 hd hs L hL hlim x1 θ C α hC K hK hdrift
  simpa [hzero] using hlim

end RobbinsMonroSA.Conv.RMFresh
end


section

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsMonroSA.Conv

/-- Theorem 2, p. 405. If `{a_n}` is of type `1/n`, if (4) holds, and if `M(x)` satisfies
(33) nondecreasing, (34) `M(θ) = α` and (35) `M′(θ) > 0`, then `lim b_n = 0`, whatever `x₁`. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (α θ : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : IsRMProcess P H a α x1 x y)
    (ha : IsTypeOneOverN a) (h33 : Monotone (regressionFn H)) (h34 : regressionFn H θ = α)
    (M' : ℝ) (h35 : HasDerivAt (regressionFn H) M' θ) (h35pos : 0 < M') :
    Tendsto (fun n => msd P x θ n) atTop (𝓝 0) := by
  obtain ⟨K,hK,hdrift⟩ := RMFresh.native_drift_eventual h4 hxy ha h33 h34 M' h35 h35pos
  exact RMFresh.rm_energy_drift_converges_zero a (msd P x θ) (dSeq P H α θ x)
    (eSeq P H α x) ha (fun n => RMFresh.msd_nonnegative n)
    (fun n => RMFresh.drift_nonnegative h33 h34 n) ((C+|α|)^2)
    (fun n => RMFresh.eSeq_bounds h4 hxy n)
    (fun n => RMFresh.native_energy_recurrence h4 hxy (fun i => (ha.1.1 i).le) n)
    x1 θ C α h4.1 K hK hdrift

end RobbinsMonroSA.Conv
end


open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : RobbinsMonroSA.Conv.BoundedResponse H C) (α θ : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : RobbinsMonroSA.Conv.IsRMProcess P H a α x1 x y)
    (ha : RobbinsMonroSA.Conv.IsTypeOneOverN a) (h33 : Monotone (RobbinsMonroSA.Conv.regressionFn H)) (h34 : RobbinsMonroSA.Conv.regressionFn H θ = α)
    (M' : ℝ) (h35 : HasDerivAt (RobbinsMonroSA.Conv.regressionFn H) M' θ) (h35pos : 0 < M') :
    Tendsto (fun n => RobbinsMonroSA.Conv.msd P x θ n) atTop (𝓝 0) := by
  exact RobbinsMonroSA.Conv.theorem_2 P H C h4 α θ a x1 x y hxy ha h33 h34 M' h35 h35pos
