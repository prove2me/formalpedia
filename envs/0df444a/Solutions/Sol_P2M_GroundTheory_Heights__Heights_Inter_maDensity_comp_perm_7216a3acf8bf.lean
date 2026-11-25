-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_maDensity_comp_perm_7216a3acf8bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:35:22.499572+00:00
-- url     : https://prove2.me/submissions/bf926908-73a3-4efe-b5cc-653bd4d0e6f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_comp_perm_4fe32ebbcec2

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (φ : Fin D → (Fin D → ℂ) → ℝ) (σ : Equiv.Perm (Fin D)) (z : Fin D → ℂ) :
    maDensity (φ ∘ σ) z = maDensity φ z := by
  unfold maDensity
  rw [show (fun k => cxHessian ((φ ∘ σ) k) z) = (fun k => cxHessian (φ k) z) ∘ σ from rfl,
    mixedDisc_comp_perm]
end GroundTheory.Heights₂.Heights.Inter
