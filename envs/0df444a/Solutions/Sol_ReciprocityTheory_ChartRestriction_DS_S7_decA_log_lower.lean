-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.decA_log_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:03:56.685571+00:00
-- url     : https://prove2.me/submissions/a124ab64-3b99-4bc8-8766-f9957901d8ce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecALogLower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_decA_exp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_decA_lead_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dec_moments
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_logSumExp_lower


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
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ} (hYp : inP ε Y)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hq : 1 ≤ q0 ε) (hpos : 0 < hs Y) (m : ℕ) (hm : m ≤ n) :
    min 1 (1 / (Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y))) *
        (∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < m ∧ m ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0) / 4 ≤
      Real.log (lead m (NormedSpace.exp Y)).re := by
  obtain ⟨h1, h2, h3, h4⟩ := dec_moments hU hY hYp m hm
  have hE : NormedSpace.exp Y = U * Matrix.diagonal (fun j => ((Real.exp (y j) : ℝ) : ℂ)) * Uᴴ := by
    rw [hY]; exact decA_exp hU y
  rw [hE, decA_lead_re y m hm, ← h3]
  have hq' : (0 : ℝ) < 2 * q0 ε := by
    have : (1 : ℝ) ≤ q0 ε := by exact_mod_cast hq
    linarith
  have hR : 0 < Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y) :=
    mul_pos (Real.sqrt_pos.mpr hq') (Real.sqrt_pos.mpr hpos)
  exact logSumExp_lower (fun J => dmW U hm J) (fun J => ∑ j ∈ J.1, y j) (fun J => by unfold dmW; positivity)
    h1 h2 hR h4
end ReciprocityTheory.ChartRestriction.DS.S7
