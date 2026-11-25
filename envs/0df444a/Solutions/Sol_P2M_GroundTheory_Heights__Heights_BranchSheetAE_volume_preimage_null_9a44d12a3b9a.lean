-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BranchSheetAE_volume_preimage_null_9a44d12a3b9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:30.664273+00:00
-- url     : https://prove2.me/submissions/3d667bac-a1b6-44f0-8848-1c4749bee9d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchSheetAE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRankDeficientFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscriminantSheetCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchSheetAE
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_of_differentiableOn_e92ad055eb8b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_injective_iff_det_ne_zero_4dda9d931b27
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.BranchSheetAE
variable {d : ℕ}
namespace GroundTheory.Heights₂.Heights.BranchSheetAE
theorem _root_.solution {G : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ} (hG : IsOpen G)
    (hF : DifferentiableOn ℂ F G) (hdet : ∀ w ∈ G, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0)
    {N : Set (Fin d → ℂ)} (hN : volume N = 0) :
    volume {t | t ∈ G ∧ F t ∈ N} = 0 := by
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hG hF
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    have hinj : Function.Injective (fderiv ℂ F w) :=
      (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hdet w hw)
    refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  apply measure_null_of_locally_null
  rintro x ⟨hxG, -⟩
  obtain ⟨e, he⟩ := hequiv x hxG
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hsymd : DifferentiableOn ℝ φ.symm (φ.target ∩ φ.symm ⁻¹' G) := by
    rintro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact (hd.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  refine ⟨{t | t ∈ G ∧ F t ∈ N} ∩ φ.source,
    inter_mem_nhdsWithin _ (φ.open_source.mem_nhds he.mem_toOpenPartialHomeomorph_source), ?_⟩
  refine measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := volume) (hsymd.mono Set.inter_subset_left) (measure_mono_null Set.inter_subset_right hN))
  rintro t ⟨⟨htG, htN⟩, hts⟩
  refine ⟨φ t, ⟨⟨φ.map_source hts, ?_⟩, ?_⟩, φ.left_inv hts⟩
  · show φ.symm (φ t) ∈ G
    rw [φ.left_inv hts]; exact htG
  · rw [hφ]; exact htN
end GroundTheory.Heights₂.Heights.BranchSheetAE
