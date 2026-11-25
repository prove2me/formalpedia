-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.psiM_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:46.291071+00:00
-- url     : https://prove2.me/submissions/6e50925b-8476-4448-81ee-1575c0aa4f5b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousConjProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_one__42e93fcaad20
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_op_one__4c551cc26830
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_psiM_kexp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_psM_one


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
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) : PsiM T μ 1 = 1 := by
  have h0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := by
    first | exact ⟨by simp [inG], by simp⟩ | exact ⟨by first | exact inG_zero ε | exact inG_zero, by simp⟩
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = toMK (1 : KG ε) * NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [toMK_one', NormedSpace.exp_zero, one_mul]
  rw [h1, psiM_kexp T μ 1 h0, op_one', one_mul, NormedSpace.exp_zero]
  first | exact psM_one T μ | exact psM_one | simp [psM_one]
end ReciprocityTheory.ChartRestriction.DS.S7
