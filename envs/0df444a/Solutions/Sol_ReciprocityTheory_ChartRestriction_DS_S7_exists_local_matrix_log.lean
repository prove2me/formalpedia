-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.exists_local_matrix_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:37.924784+00:00
-- url     : https://prove2.me/submissions/a11e98fe-5abd-41da-86ef-fd0b7e2377a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LocalA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lcA_exp_strict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ (∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (ℓ k) = k) ∧
      (∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ℓ (NormedSpace.exp Y) = Y) := by
  have hf := lcA_exp_strict (n := n)
  refine ⟨hf.localInverse _ _ _, ?_, ?_, hf.eventually_left_inverse⟩
  · have h1 := hf.localInverse_continuousAt.tendsto
    have h2 := hf.localInverse_apply_image
    rw [NormedSpace.exp_zero] at h1 h2
    rwa [h2] at h1
  · have h := hf.eventually_right_inverse
    rwa [NormedSpace.exp_zero] at h
end ReciprocityTheory.ChartRestriction.DS.S7
