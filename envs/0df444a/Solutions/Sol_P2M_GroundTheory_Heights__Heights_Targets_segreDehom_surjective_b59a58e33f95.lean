-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_segreDehom_surjective_b59a58e33f95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:39:32.98253+00:00
-- url     : https://prove2.me/submissions/fcc76f51-6448-44e3-aaff-ecb0b110e3ec

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_dehom_surjective_7ef87700430c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_segreDehom_chartSubst_45c6b3f69e75

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*}
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Function.Surjective (segreDehom σ i) := fun g => by
  obtain ⟨f, rfl⟩ := dehom_surjective i g
  exact ⟨chartSubst σ i f, segreDehom_chartSubst σ i f⟩
end GroundTheory.Heights₂.Heights.Targets
