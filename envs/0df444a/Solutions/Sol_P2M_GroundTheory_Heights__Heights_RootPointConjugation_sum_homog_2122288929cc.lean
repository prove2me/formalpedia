-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootPointConjugation_sum_homog_2122288929cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:45.816483+00:00
-- url     : https://prove2.me/submissions/435a6c4b-b911-49d0-96d8-784943170d08

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointConj

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootPointConjugation
namespace GroundTheory.Heights₂.Heights.RootPointConjugation
theorem _root_.solution {σ A : Type*} [CommRing A] (S : Finset (σ →₀ ℕ)) (N : ℕ)
    (hS : ∀ μ ∈ S, (μ.sum fun _ e => e) ≤ N) (s : A) (g : (σ →₀ ℕ) → A) :
    ∑ μ ∈ S, s ^ (N - μ.sum fun _ e => e) * (s ^ (μ.sum fun _ e => e) * g μ) = s ^ N * ∑ μ ∈ S, g μ := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ hμ => by rw [← mul_assoc, pow_sub_mul_pow _ (hS μ hμ)]
end GroundTheory.Heights₂.Heights.RootPointConjugation
