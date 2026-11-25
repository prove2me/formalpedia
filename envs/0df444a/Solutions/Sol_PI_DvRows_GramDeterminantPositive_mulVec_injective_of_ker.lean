-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.mulVec_injective_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:06.261408+00:00
-- url     : https://prove2.me/submissions/9e8f421a-248b-4a63-8c95-318360866848

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution {m k : Type*} [Fintype k] {P : Matrix m k ℂ}
    (h : ∀ v, P *ᵥ v = 0 → v = 0) : Function.Injective P.mulVec := fun a b hab =>
  sub_eq_zero.1 (h _ (by rw [mulVec_sub, hab, sub_self]))
end PI.DvRows.GramDeterminantPositive
