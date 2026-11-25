-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_OpenSetChart_maMeasure_univ_b26b934b9454
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:44:48.021799+00:00
-- url     : https://prove2.me/submissions/d78b16ae-d378-47a0-a960-4b66e3a2401e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_HypImp
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OfFubiniStudyCoverMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_OpenSetChart_measurable_retract_5a8bec867e10

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.FourB.OpenSetChart
variable {D : ℕ} {M : Set (Fin D → ℂ)}
namespace GroundTheory.Heights₂.Heights.FourB.OpenSetChart
theorem _root_.solution (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) (u : M → ℝ) :
    maMeasure (atlas hM x₀ hx₀) (fun _ => LocPot.ofFun u) Set.univ =
      ∫⁻ y in M, ENNReal.ofReal (maDens (fun _ y' => u (retract x₀ hx₀ y')) y) := by
  have hne : Nonempty (ChartPartition (atlas hM x₀ hx₀)) := ⟨partition hM x₀ hx₀⟩
  have : Subsingleton (Fin (atlas hM x₀ hx₀).n) := (inferInstance : Subsingleton (Fin 1))
  have hχ : ∀ j x, hne.some.χ j x = 1 := by
    intro j x
    have h := hne.some.sum_eq_one x
    rwa [Fintype.sum_subsingleton _ j] at h
  let j0 : Fin (atlas hM x₀ hx₀).n := ⟨0, Nat.zero_lt_one⟩
  have ht : ((atlas hM x₀ hx₀).chart j0).target = M := rfl
  have hm : Measurable ((atlas hM x₀ hx₀).chart j0).symm := measurable_retract hM hx₀
  rw [maMeasure, dif_pos hne, Fintype.sum_subsingleton _ j0,
    Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ht]
  refine lintegral_congr fun y => ?_
  rw [hχ, one_mul]
  rfl
end GroundTheory.Heights₂.Heights.FourB.OpenSetChart
