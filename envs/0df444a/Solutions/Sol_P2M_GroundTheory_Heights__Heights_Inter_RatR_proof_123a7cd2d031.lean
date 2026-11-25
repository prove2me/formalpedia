-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RatR_proof_123a7cd2d031
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:10:56.969414+00:00
-- url     : https://prove2.me/submissions/cadd2c07-0010-45e2-b18d-62429447f4c9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDerived
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PConsequences
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_tensor_sqMetric_a_2f747b7be4bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ae_eval_ne_zero_703e4b72ee63
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I2_recR_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite
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
namespace RatR
theorem _root_.solution (hInt : PtsIntegrableStatement) : RatR.Statement := by
  intro K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩
  obtain ⟨-, hAdd, hR⟩ := hI
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hAB := isSmoothHerm_tensor hA hB
  have hRf := hR P n L _ f α hP hL hAB (tensor_sqMetric_a hαβ) hf hfP
  have hRg := hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP
  have hsum := hAdd P n L A _ hP hL hA hB
  have hint : arInt P f (A.tensor (HermLine.sqMetric β)) L - arInt P g (HermLine.sqMetric β) L =
      ptsIntegral P (pot L) (logNormRat A f g) := by
    show ptsIntegral P (pot L) _ - ptsIntegral P (pot L) _ = _
    unfold ptsIntegral
    split_ifs with hΨ
    · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
      unfold ptsIntegralAt
      rw [← integral_sub (hInt K ι P n _ L _ f hP hΨg hL hAB ⟨α, tensor_sqMetric_a hαβ, hf, hfP⟩)
        (hInt K ι P n _ L _ g hP hΨg hL hB ⟨β, fun k ↦ rfl, hg, hgP⟩)]
      refine integral_congr_ae ?_
      filter_upwards [ae_eval_ne_zero hP hΨg ⟨α, hf⟩ hfP, ae_eval_ne_zero hP hΨg ⟨β, hg⟩ hgP]
        with y hyf hyg
      rw [← finsum_mem_sub_distrib _ _ (fibreFinite K ι P n _ hP hΨg y)]
      refine finsum_mem_congr rfl fun w _ ↦ ?_
      unfold sheetDensity
      split_ifs with hγ
      · have hs := hγ.choose_spec.2.self_of_nhds
        set z := hγ.choose y
        have hz : z ∈ mcPts P := hs.2.1
        have hf0 := norm_pos_iff.mpr (hyf z hz hs.2.2)
        have hg0 := norm_pos_iff.mpr (hyg z hz hs.2.2)
        have hA0 := A.pos z hz.1
        have hB0 := (HermLine.sqMetric (ι := ι) β).pos z hz.1
        rw [← sub_mul]
        congr 1
        show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (HermLine.sqMetric β).h z)) -
          Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h z) =
          Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z)
        rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
          Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
          Real.log_div hf0.ne' hg0.ne']
        ring
      · simp
    · simp
  unfold recRRat
  rw [recR_eq] at hRf hRg
  show I P (n + 1) (Fin.snoc L A) = cycR I P L f - cycR I P L g - ptsIntegral P (pot L) (logNormRat A f g)
  rw [← hint]
  linarith
end RatR
end GroundTheory.Heights₂.Heights.Inter
