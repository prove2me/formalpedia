-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_maDensity_zero_2fd3328216c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:55.687206+00:00
-- url     : https://prove2.me/submissions/b9147ee0-3602-4a03-8b4f-f10b51879a44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPtsIntegralZeroLowerNE

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.PtsIntegralZeroLowerNEAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PtsIntegralZeroLowerNEAux
theorem _root_.solution (φ : Fin 0 → (Fin 0 → ℂ) → ℝ) (z : Fin 0 → ℂ) : maDensity φ z = 1 := by
  simp [maDensity, mixedDisc, Matrix.det_fin_zero]
end GroundTheory.Heights₂.Heights.PtsIntegralZeroLowerNEAux
