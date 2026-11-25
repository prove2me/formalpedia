-- Prove2me | solution 1 for PI.WickFormula.lprod_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:18:38.35748+00:00
-- url     : https://prove2.me/submissions/29bc8e1f-051c-4d67-8f91-76d262b8d001

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
variable {AA : Type} [Ring AA]
namespace PI.WickFormula
theorem _root_.solution {n : ℕ} (c : Fin n → AA) (e : Fin n → ℕ) (h : ∀ i, e i = 0) : lprod c e = 1 := by
  unfold lprod
  simp [h]
end PI.WickFormula
