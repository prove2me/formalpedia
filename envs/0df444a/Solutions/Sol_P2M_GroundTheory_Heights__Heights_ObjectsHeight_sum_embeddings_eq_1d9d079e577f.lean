-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_sum_embeddings_eq_1d9d079e577f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:25.017796+00:00
-- url     : https://prove2.me/submissions/3e21de83-d142-4a92-ac71-ed21de9098b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (F : (K →+* ℂ) → ℝ)
    (hF : ∀ σ, F (ComplexEmbedding.conjugate σ) = F σ) :
    ∑ σ, F σ = ∑ w : InfinitePlace K, (w.mult : ℝ) * F w.embedding := by
  classical
  rw [← Finset.univ.sum_fiberwise (fun σ => InfinitePlace.mk σ) F]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F w.embedding) ?_, Finset.sum_const,
    InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff] at hσ
  rcases hσ with rfl | hσ
  · rfl
  · rw [← hσ, hF]
end GroundTheory.Heights₂.Heights.ObjectsHeight
