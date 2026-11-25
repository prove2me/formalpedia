-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_det_ne_zero_bb9babd323db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:18.669429+00:00
-- url     : https://prove2.me/submissions/540c7f21-6321-48da-9a30-b9d111faf34a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetNoChartNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_isOpen_ratPreimage_0d182ed088fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_differentiableOn_mulVec_9d66d20ccb40
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_finrank_real_fin_complex_ead260cab016
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
open GroundTheory.Heights₂.Heights.RatSheetNoChartNull
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatSheetNoChartNull
theorem _root_.solution (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ} {A : Matrix (Fin d) (Fin n) ℂ}
    (hJ : J.IsPrime) (hA : IsFiniteProjection J A)
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : RatChart.IsRatSheetAt J p q x s)
    {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : RatChart.ratMap p q x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A *ᵥ s w) w).det ≠ 0 := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set R := RatChart.ratMap p q with hRdef
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A *ᵥ s w with hFdef
  by_contra hall
  push Not at hall
  have hcrit : F '' (W₀ ∩ U) ⊆ F '' {w | w ∈ U ∧ ¬ Function.Injective (fderiv ℂ F w)} :=
    Set.image_mono fun w hw => ⟨hw.2, fun hinj => (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩
  have hnull := measure_mono_null hcrit (h₂ d d U F hU (SheetOnlyNull.differentiableOn_mulVec A hsd))
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).1
  have hqx : eval x q ≠ 0 := hsx ▸ (hsec _ hyU).2.1
  have hnhds := h₁ n d J (linPoly A) hJ hA.injective hA.finite x hxZ
    (V ∩ ({x | eval x q ≠ 0} ∩ R ⁻¹' (W₀ ∩ U)))
    (inter_mem hV ((isOpen_ratPreimage p q (hW₀.inter hU)).mem_nhds ⟨hqx, hxW₀, hyU⟩))
  have hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A i)) = A *ᵥ z := fun z => by
    ext i
    simp [linPoly, Matrix.mulVec, dotProduct]
  simp only [hev] at hnhds
  have hsub : (fun z => A *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J ∩
      (V ∩ ({x | eval x q ≠ 0} ∩ R ⁻¹' (W₀ ∩ U)))) ⊆ F '' (W₀ ∩ U) := by
    rintro _ ⟨z, ⟨hzZ, hzV, hzq, hzW⟩, rfl⟩
    refine ⟨R z, hzW, ?_⟩
    simp only [hFdef]
    rw [← hVs z ⟨hzZ, hzV⟩ hzq hzW.2]
  have hpos := Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)])
    (Filter.mem_of_superset hnhds hsub)
  rw [SheetOnlyNull.finrank_real_fin_complex] at hpos
  exact hpos.ne' hnull
end GroundTheory.Heights₂.Heights.RatSheetNoChartNull
