-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_proof_7c7673e23d37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:37:39.682397+00:00
-- url     : https://prove2.me/submissions/8f737307-e541-4974-8194-f540826d29f3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogNormGradDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogNormGradDensNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_levi_log_dualNorm_nonneg_3e81938347b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiffOn_log_dualNorm_a92d55d266bf
import Theorems.Thm_ReciprocityTheory_AnForm_A_gradDensNonneg_thm
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp


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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace LogNormGradDensNonneg
theorem _root_.solution : LogNormGradDensNonneg.Statement := by
  intro n e h s y v hs hsy
  set t : (Fin n → ℂ) → ℝ := fun x => Real.log (h.dualNorm x) with ht
  set V : Set (Fin (e + 1) → ℂ) := {z | AnalyticAt ℂ s z ∧ s z ≠ 0} with hVdef
  have hV : IsOpen V := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    filter_upwards [hz.1.eventually_analyticAt,
      hz.1.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hz.2)] with u hu hu'
    exact ⟨hu, hu'⟩
  have htc : ∀ x : Fin n → ℂ, x ≠ 0 → ContDiffAt ℝ 2 t x := fun x hx =>
    ((contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds hx)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hC : ∀ z ∈ V, ContDiffAt ℝ 2 (t ∘ s) z := fun z hz =>
    (htc (s z) hz.2).comp z (hz.1.restrictScalars (𝕜 := ℝ)).contDiffAt
  refine gradDensNonneg_thm e (fun _ => t ∘ s) v V hV
    (fun _ => fun z hz => (hC z hz).contDiffWithinAt) ?_ y ⟨hs, hsy⟩
  intro _ z hz ξ
  rw [levi_comp ξ hz.1 (htc (s z) hz.2)]
  exact LogNormGradDensNonneg.levi_log_dualNorm_nonneg h hz.2 _
end LogNormGradDensNonneg
end GroundTheory.Heights₂.Heights
