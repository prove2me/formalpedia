-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hs_exp_leVG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:53.381786+00:00
-- url     : https://prove2.me/submissions/55240407-397e-419c-b7a6-c3c36ab8a684

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_sqrt_hs_frobVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_norm_exp_frobVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_nonnegVG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) :
    hs (NormedSpace.exp X) ≤ n * Real.exp (2 * Real.sqrt (hs X)) := by
  have h := norm_exp_frobVG X
  rw [← sqrt_hs_frobVG, ← sqrt_hs_frobVG] at h
  have h0 : 0 ≤ hs (NormedSpace.exp X) := hs_nonnegVG _
  calc hs (NormedSpace.exp X) = Real.sqrt (hs (NormedSpace.exp X)) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ (Real.sqrt n * Real.exp (Real.sqrt (hs X))) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    _ = _ := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), ← Real.exp_nat_mul]
        norm_num
end ReciprocityTheory.ChartRestriction.DS.S7
