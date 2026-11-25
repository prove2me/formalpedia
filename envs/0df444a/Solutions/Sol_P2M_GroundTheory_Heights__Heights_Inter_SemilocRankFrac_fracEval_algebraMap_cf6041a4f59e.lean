-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_fracEval_algebraMap_cf6041a4f59e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:16:56.297948+00:00
-- url     : https://prove2.me/submissions/ffd46a64-ee78-41f0-936b-70dc3d4680ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocChartRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]
  (x' : (Σ k, ι' k) → Ω) (P' : Ideal (MRing ι')) [P'.IsPrime]
  (h : RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω) = P')
namespace GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
theorem _root_.solution (f : MRing ι') :
    fracEval x' P' h (algebraMap _ _ (Ideal.Quotient.mk P' f)) = aeval x' f := by
  rw [fracEval, IsFractionRing.lift_algebraMap]
  rfl
end GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
