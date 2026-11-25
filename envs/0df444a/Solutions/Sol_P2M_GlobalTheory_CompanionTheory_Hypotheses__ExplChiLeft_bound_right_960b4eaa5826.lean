-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__ExplChiLeft_bound_right_960b4eaa5826
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:52:43.875747+00:00
-- url     : https://prove2.me/submissions/546c8f6f-da4f-44d0-af3d-9b09fe3b338c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DirichletLogDerivReflectionFormulaStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundLeftRegionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DirichletLogDerivBoundLeftHalfPlane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.ExplChiLeft
namespace GlobalTheory.CompanionTheory.Hypotheses₂.ExplChiLeft
theorem _root_.solution : ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ), 3 / 2 ≤ s.re → ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ B := by
  have hsum : Summable fun n => ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) (3 / 2) n‖ :=
    (LSeriesSummable_vonMangoldt (s := 3 / 2) (by norm_num)).norm
  refine ⟨∑' n, ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) (3 / 2) n‖,
    tsum_nonneg fun _ => norm_nonneg _, ?_⟩
  intro N _ χ s hs2
  have hs : 1 < s.re := by linarith
  have h1 := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs, neg_div] at h1
  rw [← norm_neg]
  refine HasSum.norm_le_of_bounded h1 hsum.hasSum fun n => ?_
  refine (LSeries.norm_term_le s (g := fun n => (vonMangoldt n : ℂ)) ?_).trans
    (LSeries.norm_term_le_of_re_le_re _ (by simpa using hs2) n)
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
end GlobalTheory.CompanionTheory.Hypotheses₂.ExplChiLeft
