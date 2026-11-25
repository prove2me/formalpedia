-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_maDensity_update_sub_fa58ba25e45b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:15:46.573923+00:00
-- url     : https://prove2.me/submissions/a0978adc-f995-48ab-8d0d-144458bb18e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_cxHessian_sub_832eb10b8be0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_mixedDisc_update_sub_b6c43d3e209b

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergySymmetry
namespace GroundTheory.Heights₂.Heights.ChartEnergySymmetry
theorem _root_.solution {D : ℕ} (Φ : Fin D → (Fin D → ℂ) → ℝ) (p : Fin D) {f g : (Fin D → ℂ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (y : Fin D → ℂ) :
    maDensity (Function.update Φ p f) y - maDensity (Function.update Φ p g) y =
      maDensity (Function.update Φ p fun y' => f y' - g y') y := by
  have key : ∀ h : (Fin D → ℂ) → ℝ, (fun k => cxHessian (Function.update Φ p h k) y) =
      Function.update (fun k => cxHessian (Φ k) y) p (cxHessian h y) := fun h => by
    funext k
    exact Function.apply_update (fun _ h' => cxHessian h' y) Φ p h k
  simp only [maDensity, key, cxHessian_sub hf hg y, mixedDisc_update_sub, Complex.sub_re]
  ring
end GroundTheory.Heights₂.Heights.ChartEnergySymmetry
