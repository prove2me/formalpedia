-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.ta_curve_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:09.633244+00:00
-- url     : https://prove2.me/submissions/09c153a6-9b2c-4815-8fd6-b69c10f5734f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dga_exp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution (X y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * y) (-X * y) 0 := by
  have h := (dga_exp (-X)).mul_const y
  have e : (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * y) =
      fun t : ℝ => NormedSpace.exp ((t : ℂ) • -X) * y := by
    simp only [smul_neg]
  rw [e]
  exact h
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
