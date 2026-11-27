-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EnergyDensNonneg_proof_41ece1331332
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:23.466381+00:00
-- url     : https://prove2.me/submissions/ab4ec6f6-cacf-4a29-b095-68e358bfb20c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PEnergyDensNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_euclPot_ff6b1ef3877d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f
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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace EnergyDensNonneg
theorem _root_.solution : EnergyDensNonneg.Statement := by
  intro n d s y v hs
  have hV : IsOpen {z | AnalyticAt ℂ s z} := isOpen_analyticAt ℂ s
  have hC : ∀ z ∈ {z | AnalyticAt ℂ s z}, ContDiffAt ℝ 2 (euclPot ∘ s) z := fun z hz =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z
      (hz.restrictScalars (𝕜 := ℝ)).contDiffAt
  refine gradDensNonneg_thm d (fun _ => euclPot ∘ s) v _ hV
    (fun _ => fun z hz => (hC z hz).contDiffWithinAt) ?_ y hs
  intro _ z hz ξ
  rw [levi_comp ξ hz ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    TubeFormComparison.levi_euclPot]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _
end EnergyDensNonneg
end GroundTheory.Heights₂.Heights
