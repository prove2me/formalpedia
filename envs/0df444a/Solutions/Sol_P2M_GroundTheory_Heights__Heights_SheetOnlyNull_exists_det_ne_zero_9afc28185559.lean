-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetOnlyNull_exists_det_ne_zero_9afc28185559
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:38.278164+00:00
-- url     : https://prove2.me/submissions/d346d852-929a-4441-a41a-0c331ed27d88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_injective_iff_det_ne_zero_4dda9d931b27
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_finrank_real_fin_complex_ead260cab016
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_differentiableOn_mulVec_9d66d20ccb40
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
open GroundTheory.Heights₂.Heights.SheetOnlyNull
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SheetOnlyNull
theorem _root_.solution (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} (hJ : J.IsPrime) (hA' : IsFiniteProjection J A')
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : A *ᵥ x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ s w) w).det ≠ 0 := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ s w with hFdef
  by_contra hall
  push Not at hall
  have hcrit : F '' (W₀ ∩ U) ⊆ F '' {w | w ∈ U ∧ ¬ Function.Injective (fderiv ℂ F w)} :=
    Set.image_mono fun w hw => ⟨hw.2, fun hinj => (injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩
  have hnull := measure_mono_null hcrit (h₂ d d U F hU (differentiableOn_mulVec A' hsd))
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).2
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hnhds := h₁ n d J (linPoly A') hJ hA'.injective hA'.finite x hxZ
    (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ U))
    (inter_mem hV (((hW₀.inter hU).preimage hAc).mem_nhds ⟨hxW₀, hyU⟩))
  have hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A' i)) = A' *ᵥ z := fun z => by
    ext i
    simp [linPoly, Matrix.mulVec, dotProduct]
  simp only [hev] at hnhds
  have hsub : (fun z => A' *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J ∩
      (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ U))) ⊆ F '' (W₀ ∩ U) := by
    rintro _ ⟨z, ⟨hzZ, hzV, hzW⟩, rfl⟩
    refine ⟨A *ᵥ z, hzW, ?_⟩
    simp only [hFdef]
    rw [← hVs z ⟨hzZ, hzV⟩ hzW.2]
  have hpos := Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)])
    (Filter.mem_of_superset hnhds hsub)
  rw [finrank_real_fin_complex] at hpos
  exact hpos.ne' hnull
end GroundTheory.Heights₂.Heights.SheetOnlyNull
