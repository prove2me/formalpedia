-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_mass_b3b259448c07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:49.139936+00:00
-- url     : https://prove2.me/submissions/798c4e52-a990-4c9b-a626-9182e686a6bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OpenAtlasSymmEventuallyEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_symm_eventuallyEq_56d36dcbd8e2
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
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
    (Q : LocPot Ω) (F : (Fin D → ℂ) → ℝ) (hQ : ∀ x z, Q.φ x z = F z / 2) :
    maMeasure (openAtlas Ω hΩ) (fun _ => Q) Set.univ =
      ∫⁻ z in (Ω : Set (Fin D → ℂ)), ENNReal.ofReal (topDens F z) := by
  have hne : Nonempty (ChartPartition (openAtlas Ω hΩ)) := ⟨openAtlasPartition Ω hΩ⟩
  let j : Fin (openAtlas Ω hΩ).n := ⟨0, Nat.one_pos⟩
  have hχ : ∀ x, hne.some.χ j x = 1 := by
    intro x
    have h := hne.some.sum_eq_one x
    rwa [Fintype.sum_subsingleton _ j] at h
  have hT : ((openAtlas Ω hΩ).chart j).target = (Ω : Set (Fin D → ℂ)) := by
    change (Ω.openPartialHomeomorphSubtypeCoe hΩ).target = _
    simp
  have hmeas : AEMeasurable ((openAtlas Ω hΩ).chart j).symm
      (volume.restrict ((openAtlas Ω hΩ).chart j).target) :=
    ((openAtlas Ω hΩ).chart j).continuousOn_symm.aemeasurable
      ((openAtlas Ω hΩ).chart j).open_target.measurableSet
  rw [maMeasure, dif_pos hne, Measure.finsetSum_apply, Fintype.sum_subsingleton _ j,
    Measure.map_apply_of_aemeasurable (hmeas.mono_ac (withDensity_absolutelyContinuous _ _))
      MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hT]
  refine setLIntegral_congr_fun Ω.isOpen.measurableSet fun y hy => ?_
  rw [hχ, one_mul]
  congr 1
  have hev : (fun z => Q.φ (((openAtlas Ω hΩ).chart j).symm y)
      (((openAtlas Ω hΩ).chart j).symm z)) =ᶠ[𝓝 y] fun z => F z / 2 := by
    filter_upwards [openAtlas_symm_eventuallyEq Ω hΩ j F hy] with z hz
    rw [hQ, hz]
  have hH := (hev.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  unfold locDens topDens maDens maDensity mdisc mixedDisc hessC cxHessian
  simp only [hH]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
