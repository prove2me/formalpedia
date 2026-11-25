-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_InductiveIntersectionFormula_proof_1eabbcf8aa5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:08:50.515156+00:00
-- url     : https://prove2.me/submissions/257d1d1d-3e1d-4a1a-9b90-b0f5bb810bc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDerived
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PConsequences
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_congr_pts_b0afe8eda56e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_cycR_sub_vertR_ca3c50543c93
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_tensor_sqMetric_a_2f747b7be4bd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I2_recR_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_sqMetric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_tensor


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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
namespace InductiveIntersectionFormula
theorem _root_.solution : InductiveIntersectionFormula.Statement := by
  classical
  intro K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ hhor hmult hnorm
  obtain ⟨-, hAdd, hR⟩ := hI
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hRf := hR P n L _ f α hP hL (isSmoothHerm_tensor hA hB) (tensor_sqMetric_a hαβ) hf hfP
  have hRg := hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP
  have hsum := hAdd P n L A _ hP hL hA hB
  have hint : arInt P f (A.tensor (HermLine.sqMetric β)) L = arInt P g (HermLine.sqMetric β) L := by
    unfold arInt
    refine ptsIntegral_congr_pts P _ fun z hz ↦ ?_
    have hApos := A.pos z hz.1
    show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (HermLine.sqMetric β).h z)) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h z)
    rw [hnorm z hz, mul_comm (A.h z), mul_div_mul_right _ _ hApos.ne']
  have hS : (divSupp_finite P f).toFinset.filter IsHorizontal =
      (divSupp_finite P g).toFinset.filter IsHorizontal := by
    ext W
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h ↦ ⟨(hhor W h.2).1 h.1, h.2⟩, fun h ↦ ⟨(hhor W h.2).2 h.1, h.2⟩⟩
  have hcyc : cycR I P L f - vertR P L f = cycR I P L g - vertR P L g := by
    rw [cycR_sub_vertR, cycR_sub_vertR, hS]
    refine Finset.sum_congr rfl fun W hW ↦ ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hW
    rw [hmult W hW.2 ((hhor W hW.2).2 hW.1)]
  rw [recR_eq] at hRf hRg
  linarith
end InductiveIntersectionFormula
end GroundTheory.Heights₂.Heights.Inter
