-- Prove2me | solution 1 for StatComplexityDM.LinearLB.ball_family_subset_localized
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:16:47.626136+00:00
-- url     : https://prove2.me/submissions/67f24a32-a287-4ee5-8a3e-cbd7fc27ddeb

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_LinearLB_Setting

set_option autoImplicit false
open FoundationsRL.GeneralDM StatComplexityDM.LinearLB


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
    θ ∈ linLocalized piStar (ballZero d) (2 * Δ) := by
  intro π
  obtain ⟨h1, -⟩ := BFH_gap d piStar hpiStar Δ hΔ0 hΔ1 i θ hθ π
  have hpi : |(π : EuclideanSpace ℝ (Fin d)) i| ≤ 1 := by
    calc |(π : EuclideanSpace ℝ (Fin d)) i| = ‖(π : EuclideanSpace ℝ (Fin d)) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖(π : EuclideanSpace ℝ (Fin d))‖ := PiLp.norm_apply_le _ _
      _ ≤ 1 := π.2
  have h0 : gapLin piStar (ballZero d) π = 0 := by simp [gapLin, linMean, ballZero]
  rw [h0, h1, sub_zero]
  obtain ⟨hl, hr⟩ := abs_le.1 hpi
  rw [abs_le]
  constructor <;> nlinarith
