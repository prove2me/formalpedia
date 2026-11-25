-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_integral_fin_zero_ff47667ab96f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:54.309798+00:00
-- url     : https://prove2.me/submissions/a4de1cf5-2c54-4b68-8963-ebc9305d5962

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
theorem _root_.solution (F : (Fin 0 → ℂ) → ℝ) (y : Fin 0 → ℂ) : ∫ y', F y' = F y := by
  rw [Measure.volume_pi_eq_dirac y, integral_dirac]
end GroundTheory.Heights₂.Heights.PtsIntegralZeroLowerNEAux
