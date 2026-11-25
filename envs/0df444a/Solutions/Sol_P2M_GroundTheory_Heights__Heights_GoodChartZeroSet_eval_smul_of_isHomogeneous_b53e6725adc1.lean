-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_smul_of_isHomogeneous_b53e6725adc1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:20:10.437524+00:00
-- url     : https://prove2.me/submissions/203c7b58-d36c-4723-a28e-10e62347c5cc

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Ydc1_eval_smul_of_isHomogeneous__67e8aa7016c3
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
namespace GroundTheory.Heights₂.Heights.GoodChartZeroSet
theorem _root_.solution {τ : Type*} {φ : MvPolynomial τ ℂ} {n : ℕ} (hφ : φ.IsHomogeneous n)
    (c : ℂ) (w : τ → ℂ) : eval (c • w) φ = c ^ n * eval w φ :=
  _root_.P2M_UpperTheory_Reformulated_B_Ydc1_eval_smul_of_isHomogeneous__67e8aa7016c3 hφ c w
end GroundTheory.Heights₂.Heights.GoodChartZeroSet
