-- Prove2me | solution 1 for UnderstandingML.sgd_learns_convex_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T17:53:23.430664+00:00
-- url     : https://prove2.me/submissions/cf9c693b-9a5a-48a0-8cbc-03cea7e7487b

import Theorems.Thm_UnderstandingML_sgd_convex_smooth

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z] (H : Set (Vec d))
    (loss : Vec d → Z → ℝ) {β B : ℝ} (hβ : 0 < β) (hB : 0 < B)
    (hprob : ConvexSmoothBounded H loss β B) (h0 : ∀ z, loss 0 z ≤ 1)
    (hmeas : Measurable (Function.uncurry loss))
    (hgrad : Measurable (Function.uncurry fun w z ↦ gradient (fun w ↦ loss w z) w)) {ε : ℝ}
    (hε0 : 0 < ε) (T : ℕ) (hT : 12 * B ^ 2 * β / ε ^ 2 ≤ T) (D : Measure Z)
    [IsProbabilityMeasure D] :
    ∀ w ∈ H, ∫ S, risk loss D
        (sgdAverage (1 / (β * (1 + 3 / ε))) (fun w z ↦ gradient (fun w ↦ loss w z) w) S)
        ∂(iidLaw D T) ≤ risk loss D w + ε := by
  intro w hw
  obtain ⟨-, hHB, hconv, hnonneg, hsmooth⟩ := hprob
  set η := 1 / (β * (1 + 3 / ε)) with hηdef
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hT
  have hT0 : 0 < T := by exact_mod_cast hTpos
  have hη : 0 < η := by positivity
  have hηβ_eq : η * β = ε / (ε + 3) := by rw [hηdef]; field_simp
  have hηβ : η * β < 1 := by
    rw [hηβ_eq, div_lt_one (by positivity)]; linarith
  have hk : 1 / (1 - η * β) = (ε + 3) / 3 := by
    rw [hηβ_eq]; field_simp; ring
  -- Theorem 14.13 at an arbitrary comparator
  have main := fun wstar => UnderstandingML.sgd_convex_smooth loss hconv hnonneg hβ.le hsmooth
    hmeas hgrad h0 hη hηβ T hT0 D wstar
  rw [hk] at main
  -- facts about the risk
  have hrisk_nn : 0 ≤ risk loss D w := integral_nonneg fun z => hnonneg w z
  have hrisk0 : risk loss D 0 ≤ 1 := by
    have := integral_mono_of_nonneg (μ := D) (f := fun z => loss 0 z) (g := fun _ => (1 : ℝ))
      (Filter.Eventually.of_forall fun z => hnonneg 0 z) (integrable_const 1)
      (Filter.Eventually.of_forall h0)
    simpa [risk] using this
  by_cases hcase : risk loss D w ≤ 1 ∧ ε ≤ 3 / 2
  · -- compare with `w` itself
    obtain ⟨hL1, hε32⟩ := hcase
    refine (main w).trans ?_
    have hq : ‖w‖ ^ 2 / (2 * η * T) = ‖w‖ ^ 2 * β * (ε + 3) / (2 * T * ε) := by
      rw [hηdef]; field_simp
    have hwB : ‖w‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hHB w hw) 2
    have hTε : 12 * B ^ 2 * β ≤ T * ε ^ 2 := by
      rwa [div_le_iff₀ (by positivity)] at hT
    have hqb : ‖w‖ ^ 2 / (2 * η * T) ≤ ε * (ε + 3) / 24 := by
      rw [hq, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 12 * ‖w‖ ^ 2 * β ≤ T * ε ^ 2 := by nlinarith
      nlinarith
    have h1 : (ε + 3) / 3 * (risk loss D w + ‖w‖ ^ 2 / (2 * η * T)) ≤
        (ε + 3) / 3 * (risk loss D w + ε * (ε + 3) / 24) := by gcongr
    refine h1.trans ?_
    nlinarith
  · -- compare with `0`
    refine (main 0).trans ?_
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      add_zero]
    have h1 : (ε + 3) / 3 * risk loss D 0 ≤ (ε + 3) / 3 := by
      have := mul_le_mul_of_nonneg_left hrisk0 (by positivity : (0 : ℝ) ≤ (ε + 3) / 3)
      linarith
    rw [not_and_or, not_le, not_le] at hcase
    rcases hcase with h | h <;> linarith
