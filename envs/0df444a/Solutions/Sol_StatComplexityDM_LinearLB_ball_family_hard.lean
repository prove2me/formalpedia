-- Prove2me | solution 1 for StatComplexityDM.LinearLB.ball_family_hard
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:14:55.905794+00:00
-- url     : https://prove2.me/submissions/cfecd6ba-1933-44b5-b4a2-6e812cc0b241

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_LinearLB_Setting

set_option autoImplicit false
open FoundationsRL.GeneralDM StatComplexityDM.LinearLB

lemma BFH_sqrt_sq_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (a - b) ^ 2 / (a + b) := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0; subst hb0; simp
  · rw [le_div_iff₀ h]
    have hx := Real.sq_sqrt ha
    have hy := Real.sq_sqrt hb
    set x := Real.sqrt a
    set y := Real.sqrt b
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have hy0 : 0 ≤ y := Real.sqrt_nonneg _
    rw [← hx, ← hy]
    have : ((x ^ 2 - y ^ 2) ^ 2) = (x - y) ^ 2 * (x + y) ^ 2 := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith [mul_nonneg hx0 hy0]

lemma BFH_hell_rad_zero (μ : ℝ) (h : μ ∈ Set.Icc (-1 : ℝ) 1) :
    hellingerSq (rad μ) (rad 0) ≤ 3 / 4 * μ ^ 2 := by
  obtain ⟨a1, a2⟩ := h
  unfold hellingerSq rad
  rw [Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  have hx : Real.sqrt ((1 + μ) / 2) = Real.sqrt (1 + μ) / Real.sqrt 2 := Real.sqrt_div (by linarith) 2
  have hy : Real.sqrt ((1 - μ) / 2) = Real.sqrt (1 - μ) / Real.sqrt 2 := Real.sqrt_div (by linarith) 2
  have hz : Real.sqrt ((1 + 0) / 2) = 1 / Real.sqrt 2 := by
    rw [add_zero, Real.sqrt_div (by norm_num), Real.sqrt_one]
  have hz' : Real.sqrt ((1 - 0) / 2) = 1 / Real.sqrt 2 := by
    rw [sub_zero, Real.sqrt_div (by norm_num), Real.sqrt_one]
  rw [hx, hy, hz, hz']
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s2p : 0 < Real.sqrt 2 := by positivity
  set x := Real.sqrt (1 + μ) with hxd
  set y := Real.sqrt (1 - μ) with hyd
  have hx2 : x ^ 2 = 1 + μ := Real.sq_sqrt (by linarith)
  have hy2 : y ^ 2 = 1 - μ := Real.sq_sqrt (by linarith)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have expand : (x / Real.sqrt 2 - 1 / Real.sqrt 2) ^ 2 + (y / Real.sqrt 2 - 1 / Real.sqrt 2) ^ 2
      = ((x - 1) ^ 2 + (y - 1) ^ 2) / 2 := by
    field_simp
    rw [s2]
    ring
  rw [expand]
  -- need 2 - x - y ≤ 3/4 μ^2
  have hxy : (x * y) ^ 2 = 1 - μ ^ 2 := by rw [mul_pow, hx2, hy2]; ring
  set t := x * y with ht
  have ht0 : 0 ≤ t := mul_nonneg hx0 hy0
  have ht1 : t ≤ 1 := by nlinarith [sq_nonneg μ]
  have hs2 : (x + y) ^ 2 = 2 + 2 * t := by nlinarith
  have hs0 : 0 ≤ x + y := by linarith
  have key : (5 + 3 * t ^ 2) / 4 ≤ x + y := by
    apply abs_le_of_sq_le_sq' _ hs0 |>.2
    rw [hs2]
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) (by positivity : (0:ℝ) ≤ 7 + 39 * t + 9 * t ^ 2 + 9 * t ^ 3)]
  nlinarith


lemma BFH_gap (d : ℕ) (piStar : Ball d → Ball d)
    (hpiStar : IsBallArgmax piStar) (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (i : Fin d) (θ : Ball d)
    (hθ : (θ : EuclideanSpace ℝ (Fin d)) = Δ • EuclideanSpace.single i 1) (π : Ball d) :
    gapLin piStar θ π = Δ * (1 - (π : EuclideanSpace ℝ (Fin d)) i) ∧
    linMean θ π = Δ * (π : EuclideanSpace ℝ (Fin d)) i := by
  have hlin : ∀ π' : Ball d, linMean θ π' = Δ * (π' : EuclideanSpace ℝ (Fin d)) i := by
    intro π'
    unfold linMean
    rw [hθ, inner_smul_left, EuclideanSpace.inner_single_left]
    simp
  have hnorm : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = Δ := by
    rw [hθ, norm_smul]; simp [abs_of_nonneg hΔ0]
  have hei : ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ ≤ 1 := by simp
  have hmax : linMean θ (piStar θ) = Δ := by
    apply le_antisymm
    · unfold linMean
      calc inner ℝ (θ : EuclideanSpace ℝ (Fin d)) ((piStar θ : Ball d) : EuclideanSpace ℝ (Fin d))
          ≤ ‖(θ : EuclideanSpace ℝ (Fin d))‖ * ‖((piStar θ : Ball d) : EuclideanSpace ℝ (Fin d))‖ :=
            real_inner_le_norm _ _
        _ ≤ Δ * 1 := by
            rw [hnorm]
            exact mul_le_mul_of_nonneg_left (piStar θ).2 hΔ0
        _ = Δ := mul_one _
    · have := hpiStar θ ⟨EuclideanSpace.single i 1, hei⟩
      rw [hlin] at this
      simpa using this
  refine ⟨?_, hlin π⟩
  unfold gapLin
  rw [hmax, hlin]
  ring


theorem solution (d : ℕ) (piStar : Ball d → Ball d)
    (hpiStar : IsBallArgmax piStar) (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (i : Fin d) (θ : Ball d)
    (hθ : (θ : EuclideanSpace ℝ (Fin d)) = Δ • EuclideanSpace.single i 1) :
    ∀ π : Ball d,
      gapLin piStar θ π = Δ * (1 - (π : EuclideanSpace ℝ (Fin d)) i) ∧
      hellLin θ (ballZero d) π ≤ 3 / 4 * Δ ^ 2 * ((π : EuclideanSpace ℝ (Fin d)) i) ^ 2 := by
  intro π
  obtain ⟨h1, h2⟩ := BFH_gap d piStar hpiStar Δ hΔ0 hΔ1 i θ hθ π
  refine ⟨h1, ?_⟩
  have hpi : |(π : EuclideanSpace ℝ (Fin d)) i| ≤ 1 := by
    calc |(π : EuclideanSpace ℝ (Fin d)) i| = ‖(π : EuclideanSpace ℝ (Fin d)) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖(π : EuclideanSpace ℝ (Fin d))‖ := PiLp.norm_apply_le _ _
      _ ≤ 1 := π.2
  have hm : Δ * (π : EuclideanSpace ℝ (Fin d)) i ∈ Set.Icc (-1 : ℝ) 1 := by
    have : |Δ * (π : EuclideanSpace ℝ (Fin d)) i| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hΔ0]
      calc Δ * |(π : EuclideanSpace ℝ (Fin d)) i| ≤ 1 * 1 :=
          mul_le_mul hΔ1 hpi (abs_nonneg _) zero_le_one
        _ = 1 := by norm_num
    exact abs_le.1 this
  have h0 : linMean (ballZero d) π = 0 := by simp [linMean, ballZero]
  unfold hellLin linModel
  rw [h0, h2]
  have := BFH_hell_rad_zero _ hm
  calc _ ≤ 3 / 4 * (Δ * (π : EuclideanSpace ℝ (Fin d)) i) ^ 2 := this
    _ = _ := by ring
