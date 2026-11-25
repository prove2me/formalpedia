-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_mul_of_isMultiHomog_e86f9b353a4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:51:51.482618+00:00
-- url     : https://prove2.me/submissions/d09687f6-8df2-44ab-8cc0-0faac9dfcce5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_monomial_mul_7a552b775659
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] (z : (Σ k, ι k) → Φ') (j : ∀ k, ι k)
variable {z j}
namespace GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin
theorem _root_.solution [∀ k, Fintype (ι k)] (hz : ∀ k, z ⟨k, j k⟩ ≠ 0) {h : MRingOver Φ ι} {a : K → ℕ}
    (hh : IsMultiHomog h a) : aeval (affCoord z j) h * ∏ k, z ⟨k, j k⟩ ^ a k = aeval z h := by
  have hw := (Bridge.isMultiHomog_iff h a).mpr hh
  conv_rhs => rw [h.as_sum]
  conv_lhs => rw [h.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw' : Finsupp.weight (NumbersDVR.blockWeight ι) m = a := hw (mem_support_iff.mp hm)
  have hmon : monomial m (coeff m h) = coeff m h • monomial m (1 : Φ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul, map_smul, smul_mul_assoc, ← hw', aeval_monomial_mul hz]
end GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin
