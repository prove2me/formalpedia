-- Prove2me | solution 1 for TaoBR.not_parabolicRestriction_printed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:02:09.882085+00:00
-- url     : https://prove2.me/submissions/bc08baa1-d908-40ad-b933-a347704711cb

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform ContDiff

namespace TaoBR

lemma norm_mkPoint_sq {m : ℕ} (u : E m) (t : ℝ) : ‖mkPoint u t‖ ^ 2 = ‖u‖ ^ 2 + t ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, mkPoint, Fin.sum_univ_castSucc]
  simp

lemma exists_dilBump (m : ℕ) (l : ℝ) (hl : 0 < l) :
    ∃ Φ : 𝓢(E (m + 1), ℂ), (∀ w, ‖Φ w‖ ≤ 1) ∧ (∀ w, ‖w‖ ≤ l → Φ w = 1) ∧
      (∀ w, 2 * l < ‖w‖ → Φ w = 0) := by
  let b : ContDiffBump (0 : E (m + 1)) := ⟨l, 2 * l, hl, by linarith⟩
  have hc : ContDiff ℝ ∞ (fun w : E (m + 1) => ((b w : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hs : HasCompactSupport (fun w : E (m + 1) => ((b w : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  refine ⟨hs.toSchwartzMap hc, ?_, ?_, ?_⟩
  · intro w
    show ‖((b w : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg b.nonneg]; exact b.le_one
  · intro w hw
    show ((b w : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (by simpa using hw)]; simp
  · intro w hw
    show ((b w : ℝ) : ℂ) = 0
    rw [b.zero_of_le_dist (by simpa using hw.le)]; simp

lemma sq_eLpNorm_two {α : Type*} {mα : MeasurableSpace α} {F : Type*} [NormedAddCommGroup F]
    (g : α → F) (μ : Measure α) : eLpNorm g 2 μ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma lintegral_sq_schwartz {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (g : 𝓢(V, ℂ)) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2) := by
  have hi : Integrable (fun x => ‖g x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).1 (g.memLp 2)
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

lemma mem_ball_mkPoint {m : ℕ} (l : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1) (u : E m) (hu : u ∈ ball (0 : E m) (l / 2)) :
    ‖mkPoint u (‖u‖ ^ 2 / 2)‖ ≤ l := by
  rw [mem_ball_zero_iff] at hu
  have h0 := norm_nonneg u
  have h := norm_mkPoint_sq u (‖u‖ ^ 2 / 2)
  have : ‖mkPoint u (‖u‖ ^ 2 / 2)‖ ^ 2 ≤ l ^ 2 := by
    have hs : ‖u‖ ^ 2 ≤ l ^ 2 / 4 := by nlinarith
    have hs2 : ‖u‖ ^ 2 ≤ 1 / 4 := by nlinarith
    have hs3 : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
    rw [h]; nlinarith [mul_le_mul_of_nonneg_left hs2 hs3]
  exact le_of_sq_le_sq (by simpa using this) hl0.le |>.trans le_rfl

lemma claim (m : ℕ) (C : ℝ≥0)
    (hC : ∀ f : 𝓢(E (m + 1), ℂ),
        eLpNorm (paraboloidRestriction f) 2 (volume.restrict (closedBall (0 : E m) 1)) ≤
          C * eLpNorm f 2 volume)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    volume (ball (0 : E m) (l / 2)) ≤
      (C : ℝ≥0∞) ^ 2 * volume (closedBall (0 : E (m + 1)) (2 * l)) := by
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3⟩ := exists_dilBump m l hl0
  let f : 𝓢(E (m + 1), ℂ) := 𝓕⁻ Φ
  have hf : 𝓕 f = Φ := FourierInvPair.fourier_fourierInv_eq Φ
  have hf' : ∀ w, 𝓕 (f : E (m + 1) → ℂ) w = Φ w := fun w => by
    rw [← SchwartzMap.fourier_coe, hf]
  have h1 := pow_le_pow_left' (hC f) 2
  rw [mul_pow, sq_eLpNorm_two, sq_eLpNorm_two] at h1
  have h2 : ∫⁻ x, ‖f x‖ₑ ^ 2 = ∫⁻ x, ‖Φ x‖ₑ ^ 2 := by
    rw [lintegral_sq_schwartz, lintegral_sq_schwartz, ← SchwartzMap.integral_norm_sq_fourier f, hf]
  have h3 : ∫⁻ x, ‖Φ x‖ₑ ^ 2 ≤ volume (closedBall (0 : E (m + 1)) (2 * l)) := by
    calc ∫⁻ x, ‖Φ x‖ₑ ^ 2 ≤ ∫⁻ x, (closedBall (0 : E (m + 1)) (2 * l)).indicator 1 x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ closedBall (0 : E (m + 1)) (2 * l)
          · rw [Set.indicator_of_mem hx]
            have : ‖Φ x‖ₑ ≤ 1 := by
              rw [← ofReal_norm]; exact ENNReal.ofReal_le_one.2 (hΦ1 x)
            simpa using pow_le_one' this 2
          · rw [Set.indicator_of_notMem hx]
            have : Φ x = 0 := hΦ3 x (by simpa [mem_closedBall_zero_iff] using hx)
            simp [this]
      _ = _ := by rw [lintegral_indicator_one measurableSet_closedBall]
  have h4 : volume (ball (0 : E m) (l / 2)) ≤
      ∫⁻ u, ‖paraboloidRestriction f u‖ₑ ^ 2 ∂(volume.restrict (closedBall (0 : E m) 1)) := by
    calc volume (ball (0 : E m) (l / 2)) = ∫⁻ u in ball (0 : E m) (l / 2), 1 := by simp
      _ ≤ ∫⁻ u in ball (0 : E m) (l / 2), ‖paraboloidRestriction f u‖ₑ ^ 2 := by
        refine setLIntegral_mono' measurableSet_ball fun u hu => ?_
        have : paraboloidRestriction f u = 1 := by
          unfold paraboloidRestriction
          rw [hf']
          exact hΦ2 _ (mem_ball_mkPoint l hl0 hl1 u hu)
        simp [this]
      _ ≤ _ := by
        refine lintegral_mono_set ?_
        intro u hu
        rw [mem_ball_zero_iff] at hu
        rw [mem_closedBall_zero_iff]
        linarith
  calc _ ≤ _ := h4
    _ ≤ _ := h1
    _ = (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖Φ x‖ₑ ^ 2 := by rw [h2]
    _ ≤ _ := by gcongr

theorem parabolic_dev (m : ℕ) (hm : 1 ≤ m) :
    ¬ ∀ p : ℝ≥0∞, 1 ≤ p → p < ENNReal.ofReal (2 * (m + 1) / m) → ∃ C : ℝ≥0,
      ∀ f : 𝓢(E (m + 1), ℂ),
        eLpNorm (paraboloidRestriction f) p (volume.restrict (closedBall (0 : E m) 1)) ≤
          C * eLpNorm f p volume := by
  intro H
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 : (2 : ℝ≥0∞) < ENNReal.ofReal (2 * (m + 1) / m) := by
    have : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [this, ENNReal.ofReal_lt_ofReal_iff (by positivity), lt_div_iff₀ hm']
    linarith
  obtain ⟨C, hC⟩ := H 2 (by norm_num) h2
  set Vm := volume (ball (0 : E m) 1) with hVm
  set Vn := volume (ball (0 : E (m + 1)) 1) with hVn
  have hVm0 : Vm ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hVmt : Vm ≠ (⊤ : ℝ≥0∞) := measure_ball_lt_top.ne
  have hVnt : Vn ≠ (⊤ : ℝ≥0∞) := measure_ball_lt_top.ne
  set a := Vm.toReal with ha
  set b := Vn.toReal with hb
  have ha0 : 0 < a := ENNReal.toReal_pos hVm0 hVmt
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  set K : ℝ := (C : ℝ) ^ 2 * 2 ^ (m + 1) * b with hK
  have hK0 : 0 ≤ K := by positivity
  set c : ℝ := a / 2 ^ m with hc
  have hc0 : 0 < c := by positivity
  set l : ℝ := min 1 (c / (2 * (K + 1))) with hl
  have hl0 : 0 < l := lt_min one_pos (by positivity)
  have hl1 : l ≤ 1 := min_le_left _ _
  have hl2 : l ≤ c / (2 * (K + 1)) := min_le_right _ _
  have key := claim m C hC l hl0 hl1
  rw [Measure.addHaar_ball_of_pos _ _ (by positivity), Measure.addHaar_closedBall _ _ (by positivity)] at key
  simp only [finrank_euclideanSpace_fin] at key
  rw [← hVm, ← hVn, ← ENNReal.ofReal_toReal hVmt, ← ENNReal.ofReal_toReal hVnt, ← ha, ← hb] at key
  have key2 : ENNReal.ofReal ((l / 2) ^ m * a) ≤ ENNReal.ofReal ((C : ℝ) ^ 2 * ((2 * l) ^ (m + 1) * b)) := by
    convert key using 1
    · rw [ENNReal.ofReal_mul (by positivity)]
    · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by positivity)]
      simp
  have key3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key2
  have hlm : 0 < l ^ m := by positivity
  have key4 : c ≤ K * l := by
    have e1 : (l / 2) ^ m * a = l ^ m * c := by
      rw [hc, div_pow]; field_simp
    have e2 : (C : ℝ) ^ 2 * ((2 * l) ^ (m + 1) * b) = l ^ m * (K * l) := by
      rw [hK, mul_pow, pow_succ, pow_succ]; ring
    rw [e1, e2] at key3
    exact le_of_mul_le_mul_left key3 hlm
  have : K * l < c := by
    calc K * l ≤ K * (c / (2 * (K + 1))) := by gcongr
      _ = c * (K / (2 * (K + 1))) := by ring
      _ < c * 1 := by
        gcongr
        rw [div_lt_one (by positivity)]; linarith
      _ = c := mul_one c
  linarith

end TaoBR

open TaoBR in
theorem solution : type_of% @TaoBR.parabolic_dev := @TaoBR.parabolic_dev
