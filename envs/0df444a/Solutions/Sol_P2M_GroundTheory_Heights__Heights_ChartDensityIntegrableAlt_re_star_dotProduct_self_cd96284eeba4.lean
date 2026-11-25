-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_re_star_dotProduct_self_cd96284eeba4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:35:48.099872+00:00
-- url     : https://prove2.me/submissions/78d69e99-b806-4f83-99c4-93d3fb87bb7d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
namespace GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
theorem _root_.solution {e : ℕ} (z : Fin e → ℂ) : (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
end GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
