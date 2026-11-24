-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.decA_lead_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:10.657275+00:00
-- url     : https://prove2.me/submissions/93790b0f-8c63-4725-9061-8cd743e3a71d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecALogLower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lead_unitary_diag


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
theorem _root_.solution {U : Matrix (Fin n) (Fin n) ℂ} (y : Fin n → ℝ) (i : ℕ) (hi : i ≤ n) :
    (lead i (U * Matrix.diagonal (fun j => ((Real.exp (y j) : ℝ) : ℂ)) * Uᴴ)).re =
      ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J * Real.exp (∑ j ∈ J.1, y j) := by
  rw [lead_unitary_diag _ i hi, Complex.re_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [show (∏ j ∈ J.1, ((Real.exp (y j) : ℝ) : ℂ)) = ((∏ j ∈ J.1, Real.exp (y j) : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul, Complex.ofReal_re, ← Real.exp_sum]
  rfl
end ReciprocityTheory.ChartRestriction.DS.S7
