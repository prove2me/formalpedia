-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_ptsIntegral_logNormRat_c623369832a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:56:21.098996+00:00
-- url     : https://prove2.me/submissions/5a6d03e2-ae43-48dd-9d14-34f8ba6278ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsIntegralLogNormRat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_ae_eval_ne_zero_511da99b05d4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
  ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral
theorem _root_.solution (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    {L : Fin n → HermLine ι} {A B : HermLine ι} {f g : MRing ι} (hP : IsArithVar P (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hf : IsSectionOn P (A.tensor B) f) (hg : IsSectionOn P B g) :
    ptsIntegral P (pot L) (logNormRat A f g) =
      ptsIntegral P (pot L) (logNorm (A.tensor B) f) - ptsIntegral P (pot L) (logNorm B g) := by
  have hAB := isSmoothHerm_tensor hA hB
  obtain ⟨α, -, hfα, hfP⟩ := id hf
  obtain ⟨β, -, hgβ, hgP⟩ := id hg
  unfold ptsIntegral
  split_ifs with hΨ
  · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
    unfold ptsIntegralAt
    rw [← integral_sub (hInt K ι P n _ L _ f hP hΨg hL hAB hf) (hInt K ι P n _ L _ g hP hΨg hL hB hg)]
    refine integral_congr_ae ?_
    filter_upwards [ae_eval_ne_zero hP hΨg ⟨α, hfα⟩ hfP, ae_eval_ne_zero hP hΨg ⟨β, hgβ⟩ hgP]
      with y hyf hyg
    rw [← finsum_mem_sub_distrib _ _ (fibreFinite K ι P n _ hP hΨg y)]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hs := hγ.choose_spec.2.self_of_nhds
      set z := hγ.choose y
      have hz : z ∈ mcPts P := hs.2.1
      have hf0 := norm_pos_iff.mpr (hyf z hz hs.2.2)
      have hg0 := norm_pos_iff.mpr (hyg z hz hs.2.2)
      have hA0 := A.pos z hz.1
      have hB0 := B.pos z hz.1
      rw [← sub_mul]
      congr 1
      show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z) =
        Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * B.h z)) -
          Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / B.h z)
      rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
        Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
        Real.log_div hf0.ne' hg0.ne']
      ring
    · simp
  · simp
end GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral
