-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_isPsh_bba4d872c2eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:43.213685+00:00
-- url     : https://prove2.me/submissions/e09d28a9-416d-41e0-a386-7ccc37ae47fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OpenAtlasSymmEventuallyEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_symm_eventuallyEq_56d36dcbd8e2
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
theorem _root_.solution {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω)
    (Q : LocPot Ω) (F : (Fin D → ℂ) → ℝ) (hQ : ∀ x z, Q.φ x z = F z / 2)
    (hF : ContDiffOn ℝ ∞ F Ω) (hL : ∀ z ∈ (Ω : Set (Fin D → ℂ)), ∀ w, 0 ≤ leviForm F z w) :
    IsPsh (openAtlas Ω hΩ) Q := by
  intro x j y hy w
  have hyΩ : y ∈ (Ω : Set (Fin D → ℂ)) := by
    have h := hy.1
    change y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target at h
    simpa using h
  have hev : (Q.φ x ∘ ((openAtlas Ω hΩ).chart j).symm) =ᶠ[𝓝 y]
      fun z => (fun _ => (0 : ℝ)) z + (1 / 2 : ℝ) * F z := by
    filter_upwards [openAtlas_symm_eventuallyEq Ω hΩ j F hyΩ] with z hz
    simp only [Function.comp_apply, hQ, hz]
    ring
  have hC : ContDiffAt ℝ 2 F y :=
    (hF.contDiffAt (Ω.isOpen.mem_nhds hyΩ)).of_le (WithTop.coe_le_coe.2 le_top)
  rw [levi_congr hev, levi_add_smul (f := fun _ => (0 : ℝ)) (1 / 2) contDiffAt_const hC]
  have h0 : levi (fun _ : Fin D → ℂ => (0 : ℝ)) y w = 0 := by simp [levi]
  have h1 : levi F y w = leviForm F y w := rfl
  have h2 := hL y hyΩ w
  rw [h0, h1]
  linarith
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
