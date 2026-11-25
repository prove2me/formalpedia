-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_exists_segre_smul_bfffda87fde7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:09:44.665662+00:00
-- url     : https://prove2.me/submissions/c2f85c3b-b924-4bd1-b8f6-aa2763ee6f9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneousAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_segre_scaleBlock_998cc66d6614
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
namespace GroundTheory.Heights₂.Heights.GoodChartZeroSet
theorem _root_.solution (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) {c : ℂ} (hc : c ≠ 0) (hK : IsEmpty K → c = 1) :
    ∃ z' ∈ mcPts P, segre z' = c • segre z := by
  classical
  by_cases h : IsEmpty K
  · exact ⟨z, hz, by rw [hK h, one_smul]⟩
  · obtain ⟨k0⟩ := not_isEmpty_iff.1 h
    exact ⟨scaleBlock k0 c z, scaleBlock_mem_zeroLocus P hP k0 hc hz, segre_scaleBlock k0 c z⟩
end GroundTheory.Heights₂.Heights.GoodChartZeroSet
