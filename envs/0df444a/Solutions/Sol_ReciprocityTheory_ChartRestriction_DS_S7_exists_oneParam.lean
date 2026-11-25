-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.exists_oneParam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:45.545803+00:00
-- url     : https://prove2.me/submissions/c008a7ac-a9ab-452a-88d9-92634801106b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFactsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_kfa_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_kfa_continuous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_kfa_toMK


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    ∃ γ : ℝ → KG ε, Continuous γ ∧ (∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) ∧
      ∀ s t, γ (s + t) = γ s * γ t := by
  exact ⟨kfaKG ε hY, kfa_continuous ε hY, kfa_toMK ε hY, kfa_add ε hY⟩
end ReciprocityTheory.ChartRestriction.DS.S7
