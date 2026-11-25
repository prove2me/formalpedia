-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.decA_hs_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:07.021149+00:00
-- url     : https://prove2.me/submissions/5f106de6-f4bb-417b-8475-7987f0d2a16c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecALogLower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_decA_hs_trace

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
theorem _root_.solution {K : Matrix (Fin n) (Fin n) ℂ} (hK : K * Kᴴ = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    hs (Kᴴ * X * K) = hs X := by
  apply Complex.ofReal_injective
  rw [decA_hs_trace, decA_hs_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc Matrix.trace (Kᴴ * X * K * (Kᴴ * (Xᴴ * K))) = Matrix.trace (Kᴴ * ((X * Xᴴ) * K)) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc K Kᴴ, hK, Matrix.one_mul]
    _ = Matrix.trace ((X * Xᴴ) * K * Kᴴ) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (X * Xᴴ) := by rw [Matrix.mul_assoc, hK, Matrix.mul_one]
end ReciprocityTheory.ChartRestriction.DS.S7
