-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_cover_le_volume_thickening_5b3271255eb1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:32:01.26915+00:00
-- url     : https://prove2.me/submissions/9415b638-56df-4b90-b8c4-0819f4ca27e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetBallCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_volume_ball_pi_complex_2b227a46408d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ComplexSets Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} {A : Set (Fin n → ℂ)} (hA : IsCompact A) {r : ℝ}
    (hr : 0 < r) : ∃ T : Finset (Fin n → ℂ), (↑T : Set (Fin n → ℂ)) ⊆ A ∧ A ⊆ ⋃ c ∈ T, ball c r ∧
      (T.card : ℝ) * (Real.pi * (r / 4) ^ 2) ^ n ≤ (volume (thickening r A)).toReal := by
  set δ : NNReal := ⟨r / 4, by positivity⟩
  have hδ : (δ : ℝ) = r / 4 := rfl
  have hpack : packingNumber (2 * δ) A ≠ ⊤ := by
    obtain ⟨N, -, hNfin, hN⟩ := exists_finite_isCover_of_isCompact (ε := δ)
      (by rw [ne_eq, ← NNReal.coe_eq_zero, hδ]; positivity) hA
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.2 hNfin)
      ((packingNumber_two_mul_le_externalCoveringNumber δ A).trans hN.externalCoveringNumber_le_encard)
  set S := maximalSeparatedSet (2 * δ) A
  have hSfin : S.Finite := Set.encard_ne_top_iff.1 (by rw [encard_maximalSeparatedSet hpack]; exact hpack)
  refine ⟨hSfin.toFinset, by simpa using maximalSeparatedSet_subset, ?_, ?_⟩
  · refine ((isCover_maximalSeparatedSet hpack).subset_iUnion_closedBall).trans ?_
    refine Set.iUnion₂_subset fun c hc => ?_
    refine (closedBall_subset_ball ?_).trans (Set.subset_biUnion_of_mem (u := fun c => ball c r) ?_)
    · simp only [NNReal.coe_mul, NNReal.coe_ofNat, hδ]; linarith
    · simpa using hc
  · have hsep := isSeparated_maximalSeparatedSet (ε := 2 * δ) (A := A)
    have hdisj : (↑hSfin.toFinset : Set (Fin n → ℂ)).PairwiseDisjoint (fun c => ball c (r / 4)) := by
      intro x hx y hy hxy
      apply ball_disjoint_ball
      have h1 : ((2 * δ : NNReal) : ENNReal) < edist x y := hsep (by simpa using hx) (by simpa using hy) hxy
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h1
      simp only [NNReal.coe_mul, NNReal.coe_ofNat, hδ] at h1
      linarith
    have hsub : (⋃ c ∈ hSfin.toFinset, ball c (r / 4)) ⊆ thickening r A := by
      refine Set.iUnion₂_subset fun c hc => ?_
      exact (ball_subset_thickening (maximalSeparatedSet_subset (by simpa using hc)) _).trans
        (thickening_mono (by linarith) A)
    have hvol := measure_mono (μ := volume) hsub
    rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at hvol
    simp only [volume_ball_pi_complex _ (by positivity : (0 : ℝ) < r / 4), Finset.sum_const,
      nsmul_eq_mul] at hvol
    have hfin : volume (thickening r A) ≠ ⊤ := (hA.isBounded.thickening).measure_lt_top.ne
    have := ENNReal.toReal_mono hfin hvol
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at this
end GroundTheory.Heights₂.Heights
