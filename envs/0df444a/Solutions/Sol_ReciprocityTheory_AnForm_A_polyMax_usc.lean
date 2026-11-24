-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.polyMax_usc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:51.085546+00:00
-- url     : https://prove2.me/submissions/0409c5c6-613c-4048-8a43-79f0fa7ad540

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_polyMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_polyMax_attained

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
noncomputable section
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (hU : IsOpen U) (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (ht : 0 ≤ t)
    (h : closedBall z t ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, closedBall z (t + δ) ⊆ U ∧
      ∀ t', 0 ≤ t' → t' ≤ t + δ → polyMax φ z t' < polyMax φ z t + ε := by
  set V : Set (Fin D → ℂ) := {x | x ∈ U ∧ φ x < polyMax φ z t + ε} with hVdef
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxU, hx⟩
    have h1 := hφ x hxU _ hx
    rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)] at h1
    filter_upwards [h1, hU.mem_nhds hxU] with y hy hyU using ⟨hyU, hy⟩
  have hsub : closedBall z t ⊆ V := fun x hx =>
    ⟨h hx, lt_of_le_of_lt (le_polyMax hφ h hx) (by linarith)⟩
  obtain ⟨δ, hδ, hδV⟩ := (isCompact_closedBall z t).exists_cthickening_subset_open hV hsub
  rw [cthickening_closedBall hδ.le ht, add_comm δ t] at hδV
  have hVU : closedBall z (t + δ) ⊆ U := fun x hx => (hδV hx).1
  refine ⟨δ, hδ, hVU, fun t' ht' ht'le => ?_⟩
  have hsub' : closedBall z t' ⊆ closedBall z (t + δ) := closedBall_subset_closedBall ht'le
  obtain ⟨x, hx, hxe⟩ := polyMax_attained hφ ht' (hsub'.trans hVU)
  rw [← hxe]
  exact (hδV (hsub' hx)).2
end ReciprocityTheory.AnForm.A
