-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chart_eval_1bd45c2a4563
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:20.730898+00:00
-- url     : https://prove2.me/submissions/859c84b1-81cb-4539-b4e5-5031f8069c69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
theorem _root_.solution {P : Ideal (MRing ι)} (τ : funField P →+* ℂ) (r : (Σ k, ι k) → funField P)
    (f : MRing ι) : τ (chartHom r f) = eval (fun p => τ (r p)) (map (Int.castRingHom ℂ) f) := by
  have : τ.comp (chartHom r) = (eval (fun p => τ (r p))).comp (map (Int.castRingHom ℂ)) :=
    MvPolynomial.ringHom_ext (fun n => by simp [chartHom]) (fun p => by simp [chartHom])
  exact congrArg (fun φ => φ f) this
end GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
