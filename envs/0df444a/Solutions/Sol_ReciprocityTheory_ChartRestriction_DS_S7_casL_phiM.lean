-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.casL_phiM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:43.047889+00:00
-- url     : https://prove2.me/submissions/f623f7f4-0b64-4f15-a8c7-ed746603e477

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_lhol_phiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_sum_casCoef


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
theorem _root_.solution (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : casL (PhiM μ) z = ((casVal lam : ℝ) : ℂ) * PhiM μ z := by
  show ∑ a, ∑ b, Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (PhiM μ)) z = _
  simp only [lhol_lhol_phiM μ _ _ hz, ← Finset.sum_mul]
  rw [← sum_casCoef μ lam hμ]
  push_cast
  rfl
end ReciprocityTheory.ChartRestriction.DS.S7
