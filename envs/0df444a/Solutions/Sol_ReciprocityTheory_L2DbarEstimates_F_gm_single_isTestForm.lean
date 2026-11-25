-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.gm_single_isTestForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:37:16.272893+00:00
-- url     : https://prove2.me/submissions/70fb7e8c-fa70-4b89-a6df-6224e829fead

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : SmoothR n z ph)
    (φ : M → ℂ) (hφ : IsTest n z φ) (j : Fin n) : IsTestForm n z (gmSingle ph φ j) := by
  intro k
  have hE : Ck n z 2 (fun y => (Real.exp (ph y) : ℂ)) := by
    simpa using gm_exp_ck n z ph hph 1 2
  have hc : Ck n z 2 (fun y => conj (φ y)) := by
    intro e he
    have h := (hφ.1 e he).of_le (natCast_le_coe_infty 2)
    have := Complex.conjCLE.contDiff.comp_contDiffOn h
    simpa [Function.comp_def] using this
  by_cases hk : k = j
  · subst hk
    refine ⟨?_, ?_⟩
    · simpa [gmSingle] using Ck.mul n z 2 _ _ hE hc
    · exact gm_hcs_of _ _ hφ.2 fun x hx => by simp [gmSingle, hx]
  · refine ⟨?_, ?_⟩
    · simpa [gmSingle, hk] using Ck.const n z 2 0
    · exact gm_hcs_of _ _ hφ.2 fun x _ => by simp [gmSingle, hk]
end ReciprocityTheory.L2DbarEstimates.F
