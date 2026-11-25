-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.greenCoord_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:06.962838+00:00
-- url     : https://prove2.me/submissions/168d216b-cce1-44f9-b285-747b9be28b06

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Theorems.Thm_ReciprocityTheory_AnForm_A_uPair_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_uPair_hasCompactSupport
import Theorems.Thm_ReciprocityTheory_AnForm_A_ddcCoordDens_insertNth
import Theorems.Thm_ReciprocityTheory_AnForm_A_greenParam_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Laplacian Pointwise
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : GreenCoordStatement := by
  intro D j u hu hs
  obtain ⟨hI, hE⟩ := greenParam_thm (Fin D → ℂ) (volume : Measure (Fin D → ℂ)) (uPair j u)
    (uPair_contDiff j hu) (uPair_hasCompactSupport j hs)
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) j).symm
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) j with he_def
  have he : ∀ q : ℂ × (Fin D → ℂ), e.symm q = Fin.insertNth j q.1 q.2 := fun q => by
    rw [he_def, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  have hg : (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z) ∘ e.symm =
      fun q => (1 / (2 * Real.pi)) * (Real.log ‖q.1‖ * Δ (fun w' : ℂ => uPair j u (w', q.2)) q.1) := by
    funext q
    simp only [Function.comp_apply, he]
    rw [Fin.insertNth_apply_same, ddcCoordDens_insertNth j hu]
    ring
  refine ⟨?_, ?_⟩
  · rw [← hmp.integrable_comp_emb e.symm.measurableEmbedding, hg, Measure.volume_eq_prod]
    exact hI.const_mul _
  · have h1 := hmp.integral_comp' (f := e.symm)
      (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z)
    rw [← h1]
    have h2 : (fun q => (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z) (e.symm q)) =
        fun q => (1 / (2 * Real.pi)) * (Real.log ‖q.1‖ * Δ (fun w' : ℂ => uPair j u (w', q.2)) q.1) := hg
    rw [h2, Measure.volume_eq_prod, integral_const_mul, hE]
    simp only [uPair]
    field_simp
end ReciprocityTheory.AnForm.A
