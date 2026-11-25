-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_arInt_mul_8727189e8376
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:39.859548+00:00
-- url     : https://prove2.me/submissions/c1ddd82f-3504-4003-9e42-49fe11046297

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PConsequences
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArIntMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ae_eval_ne_zero_703e4b72ee63
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite


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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    (hP : IsArithVar P (n + 1)) {L : Fin n → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) :
    arInt P (s * t) (A.tensor B) L = arInt P s A L + arInt P t B L := by
  obtain ⟨a, -, hsa, hsP⟩ := id hs
  obtain ⟨b, -, htb, htP⟩ := id ht
  show ptsIntegral P (pot L) _ = ptsIntegral P (pot L) _ + ptsIntegral P (pot L) _
  unfold ptsIntegral
  split_ifs with hΨ
  · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
    unfold ptsIntegralAt
    rw [← integral_add (hInt K ι P n _ L A s hP hΨg hL hA hs) (hInt K ι P n _ L B t hP hΨg hL hB ht)]
    refine integral_congr_ae ?_
    filter_upwards [ae_eval_ne_zero hP hΨg ⟨a, hsa⟩ hsP, ae_eval_ne_zero hP hΨg ⟨b, htb⟩ htP]
      with y hys hyt
    rw [← finsum_mem_add_distrib' ((fibreFinite K ι P n _ hP hΨg y).subset Set.inter_subset_left)
      ((fibreFinite K ι P n _ hP hΨg y).subset Set.inter_subset_left)]
    refine finsum_mem_congr rfl fun w _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hsh := hγ.choose_spec.2.self_of_nhds
      set z := hγ.choose y
      have hz : z ∈ mcPts P := hsh.2.1
      have hs0 := norm_pos_iff.mpr (hys z hz hsh.2.2)
      have ht0 := norm_pos_iff.mpr (hyt z hz hsh.2.2)
      have hA0 := A.pos z hz.1
      have hB0 := B.pos z hz.1
      rw [← add_mul]
      congr 1
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (s * t))‖ / (A.h z * B.h z)) =
        Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z) +
          Real.log (‖eval z (map (Int.castRingHom ℂ) t)‖ / B.h z)
      rw [map_mul, map_mul, norm_mul, mul_div_mul_comm]
      exact Real.log_mul (div_pos hs0 hA0).ne' (div_pos ht0 hB0).ne'
    · simp
  · simp
end GroundTheory.Heights₂.Heights.Inter
