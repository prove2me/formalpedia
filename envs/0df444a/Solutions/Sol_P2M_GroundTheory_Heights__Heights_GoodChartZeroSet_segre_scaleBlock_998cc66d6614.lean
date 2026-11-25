-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_segre_scaleBlock_998cc66d6614
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:32:59.069797+00:00
-- url     : https://prove2.me/submissions/0c1bcebd-b431-4379-943b-537c54126a2f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneousAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Finset
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets
open GroundTheory.Heights₂.Heights.GoodChartZeroSet
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.GoodChartZeroSet
theorem _root_.solution [DecidableEq K] (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (scaleBlock k0 c z) = c • segre z := by
  funext j
  show ∏ k, (if k = k0 then c else 1) * z ⟨k, j k⟩ = c * ∏ k, z ⟨k, j k⟩
  rw [Finset.prod_mul_distrib]
  simp
end GroundTheory.Heights₂.Heights.GoodChartZeroSet
