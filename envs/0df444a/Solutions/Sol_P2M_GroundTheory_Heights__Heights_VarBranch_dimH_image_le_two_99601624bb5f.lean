-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarBranch_dimH_image_le_two_99601624bb5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:22:45.31328+00:00
-- url     : https://prove2.me/submissions/55a7b620-2a31-4290-868f-454216c47de4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchGermDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroDimIsolated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimComponentBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchGermDimOne

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
open MvPolynomial ComplexSets Filter Topology
open scoped NNReal ENNReal
namespace GroundTheory.Heights₂.Heights
namespace VarBranch
theorem _root_.solution {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (c : VarBranch I 1 q) : dimH c.image ≤ 2 := by
  let ι : ℂ → (Fin 1 → ℂ) := fun τ _ ↦ τ
  have hι : ∀ τ : ℂ, ‖ι τ‖ = ‖τ‖ := fun τ ↦ by simp [ι, pi_norm_const]
  have himg : c.image = (c.toFun ∘ ι) '' Metric.ball 0 c.radius := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t 0, ?_, ?_⟩
      · have h0 : ‖t 0‖ ≤ ‖t‖ := norm_le_pi_norm t 0
        rw [Metric.mem_ball, dist_zero_right] at ht ⊢
        linarith
      · simp only [Function.comp, ι]
        congr 1
        funext i
        rw [Subsingleton.elim i 0]
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨ι τ, ?_, rfl⟩
      rw [Metric.mem_ball, dist_zero_right] at hτ ⊢
      rwa [hι]
  have hd : DifferentiableOn ℂ (c.toFun ∘ ι) (Metric.ball 0 c.radius) := by
    have hιd : Differentiable ℂ ι := differentiable_pi.2 fun _ ↦ differentiable_id
    refine c.differentiableOn.comp hιd.differentiableOn fun τ hτ ↦ ?_
    rw [Metric.mem_ball, dist_zero_right] at hτ ⊢
    rwa [hι]
  have hcd : ContDiffOn ℝ 1 (c.toFun ∘ ι) (Metric.ball 0 c.radius) :=
    (hd.contDiffOn Metric.isOpen_ball).restrict_scalars ℝ
  rw [himg]
  calc dimH ((c.toFun ∘ ι) '' Metric.ball 0 c.radius) ≤ dimH (Metric.ball (0 : ℂ) c.radius) :=
        hcd.dimH_image_le (convex_ball 0 c.radius) le_rfl
    _ ≤ dimH (Set.univ : Set ℂ) := dimH_mono (Set.subset_univ _)
    _ = 2 := by rw [Real.dimH_univ_eq_finrank ℂ, Complex.finrank_real_complex]; norm_num
end VarBranch
end GroundTheory.Heights₂.Heights
