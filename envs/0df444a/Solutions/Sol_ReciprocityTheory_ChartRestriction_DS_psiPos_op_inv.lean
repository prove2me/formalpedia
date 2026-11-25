-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.psiPos_op_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:40.660828+00:00
-- url     : https://prove2.me/submissions/52ce0c94-ad7e-44e8-927e-e9cb0536a177

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_KinstSecondCountable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_PsiPos

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
theorem _root_.solution (T : KType ε Λ) (k : KG ε) :
    T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
  simp only [KType.op]
  rw [map_inv, ← ContinuousLinearMap.star_eq_adjoint]
  first
    | rfl
    | (rw [← unitary.star_eq_inv]; rfl)
    | simp
end ReciprocityTheory.ChartRestriction.DS
