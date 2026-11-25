-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.psiPos_inner_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:51.962911+00:00
-- url     : https://prove2.me/submissions/dce4191a-db83-41ad-963e-5e510849c34d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_KinstSecondCountable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_PsiPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_psiPos_op_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open S7
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (T : KType ε Λ) (k : KG ε) (v : T.V) :
    ⟪v, (T.op k * projW T * T.op k⁻¹) v⟫_ℂ = ((‖⟪T.op k T.w, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [psiPos_op_inv T k]
  simp only [ContinuousLinearMap.mul_apply, projW, ContinuousLinearMap.smulRight_apply,
    map_smul, inner_smul_right]
  rw [← inner_conj_symm v (T.op k T.w)]
  rw [show ((innerSL ℂ) T.w) (ContinuousLinearMap.adjoint (T.op k) v) = ⟪T.op k T.w, v⟫_ℂ from
    ContinuousLinearMap.adjoint_inner_right _ _ _]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
end ReciprocityTheory.ChartRestriction.DS
