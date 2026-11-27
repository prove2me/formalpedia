-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BoundedMonomials_proof_7c784f48e4b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:57:23.065106+00:00
-- url     : https://prove2.me/submissions/0297562a-ae1d-4807-a9ee-1dfdb5b25f81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_X_bd364b1db4a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_eq_93aea306bd91
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_exists_bound_chart_c83e86b47d1f

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
namespace GroundTheory.Heights₂.Heights.BoundedMonomials
theorem _root_.solution : BoundedMonomials.Statement := by
  intro ι _ _ n P A s
  refine ⟨fun z hz c c' d d' e e' he he' hc hc' ↦ chartNorm_eq s hz he he' hc hc', ?_⟩
  choose B hB using exists_bound_chart s
  refine ⟨Real.log (∑ c, |B c| + 1), fun z hz c d e he hc ↦ ?_⟩
  have hS : 0 < ∑ c, |B c| + 1 := by positivity
  rw [Real.exp_log hS]

  have hmax : ∀ k, ∃ i, ∀ j, ‖z k j‖ ≤ ‖z k i‖ := fun k ↦ by
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j ↦ ‖z k j‖) Finset.univ_nonempty
    exact ⟨i, fun j ↦ hi j (Finset.mem_univ j)⟩
  choose c₀ hc₀ using hmax
  have hc₀z : ∀ k, z k (c₀ k) ≠ 0 := fun k h0 ↦ by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (hz.1 k)
    have := hc₀ k j
    rw [h0, norm_zero] at this
    exact hj (norm_le_zero_iff.mp this)
  have hlive : ∀ k, (X ⟨k, c₀ k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦ by
    have h0 := hz.2 _ hk
    rw [evalCone_X] at h0
    exact hc₀z k h0
  obtain ⟨d₀, e₀, he₀⟩ := s.regular c₀ hlive
  change chartNorm A c d e z ≤ _
  rw [chartNorm_eq s hz he he₀ hc hc₀z]
  calc chartNorm A c₀ d₀ e₀ z ≤ B c₀ := hB c₀ z hz hc₀z hc₀ d₀ e₀ he₀
    _ ≤ |B c₀| := le_abs_self _
    _ ≤ ∑ c, |B c| := Finset.single_le_sum (fun c _ ↦ abs_nonneg (B c)) (Finset.mem_univ c₀)
    _ ≤ ∑ c, |B c| + 1 := by linarith
end GroundTheory.Heights₂.Heights.BoundedMonomials
