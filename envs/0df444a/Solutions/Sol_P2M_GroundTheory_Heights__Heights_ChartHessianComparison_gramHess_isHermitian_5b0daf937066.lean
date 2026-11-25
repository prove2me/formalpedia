-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_gramHess_isHermitian_5b0daf937066
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:37.243652+00:00
-- url     : https://prove2.me/submissions/382c394e-78c5-43fa-9960-9667eb6730d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.ChartHessianComparison
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartHessianComparison
theorem _root_.solution (u : F) (d : Fin e → F) : (gramHess u d).IsHermitian := by
  ext i j
  simp only [gramHess, conjTranspose_apply, of_apply, star_div₀, star_sub, star_mul', star_pow,
    Complex.star_def, inner_conj_symm, map_ofNat]
  ring
end GroundTheory.Heights₂.Heights.ChartHessianComparison
